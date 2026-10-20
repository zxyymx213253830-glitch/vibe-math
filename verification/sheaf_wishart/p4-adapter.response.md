# P4 Adversarial Code Review: Bounded Windows SHEAF Adapter

## 1. Concurrency/Atomicity: TOCTOU in `exclusive` Lock (Severity: High, Scope: All lock-protected operations)

```python
def exclusive(path, group):
    path = Path(path)
    token = uuid.uuid4().hex
    path.parent.mkdir(parents=True, exist_ok=True)
    fd = os.open(path, os.O_CREAT | os.O_EXCL | os.O_WRONLY)  # atomic create
    with os.fdopen(fd, "w", encoding="utf-8") as out:
        json.dump(dict(token=token, group=group, pid=os.getpid(), started_utc=now()), out)
```

**Defect:** `os.O_EXCL` guarantees atomic file creation, but the JSON payload is written *after* the file exists. A concurrent reader calling `read(path)` between `os.open` and `json.dump` completion will get a `JSONDecodeError` on an empty/partial file. The docstring claims "Never take over or delete another owner's claim" but provides no atomic-write guarantee for the claim contents themselves.

**Impact:** `check()` acquires two `exclusive` locks then calls `validate_locks()` which reads files. A concurrent process reading `operation.lock` during creation crashes.

---

## 2. Correctness: `lease()` Pre-check is Purely Advisory / TOCTOU (Severity: High, Scope: Lifecycle closing leases)

```python
def lease():
    for name in ("STOP", "compute.lock", "CODEX_REVIEW", "runner.lock"):
        if (SESSION / name).exists():
            raise ValueError(...)
    state = read(SESSION / "state.json")
    if state.get("stage", "").startswith("ACTIVE"):
        raise ValueError(...)
    # ... writes state ...
```

**Defect:** The existence checks and stage check are non-atomic with respect to the subsequent `write()`. Two concurrent adapter invocations can both pass the guard, then both write `ACTIVE_SHEAF_BOUNDED_CHECK` state. There is no `os.O_EXCL` or file-level locking on `state.json` itself.

Additionally, `compute.lock` is documented as the central serialization point for Lean runs, but this adapter never acquires it—it only checks for its existence. If the intent is that `lease()` substitutes for `compute.lock`, this is undocumented; if not, the adapter can run concurrent Lean compilations against the stated invariant.

**Impact:** Violates "all Lean runs ONLY through collaborative_check.py under one central compute.lock."

---

## 3. Correctness: Stale Deadline Never Enforced (Severity: Medium, Scope: Lifecycle closing leases)

```python
state.update(..., deadline_utc=(datetime.now(timezone.utc) + timedelta(minutes=15)).isoformat(), ...)
```

**Defect:** `deadline_utc` is written but never read or enforced anywhere in the adapter. If a `check()` invocation hangs indefinitely (e.g., `collaborative_check.py` blocks), the lease remains `ACTIVE_SHEAF_BOUNDED_CHECK` forever. The `finally` block only runs if control returns to it.

**Impact:** A hung subprocess creates a permanent stale lease, blocking all future `check()` and `accept()` calls until manual intervention.

---

## 4. Correctness: `gated()` Success Regex Misses Uppercase/Variant Diagnostics (Severity: Medium, Scope: Failure/stale evidence acceptance)

```python
success=code == 0 and log.exists() and before == sha(source) and
        not re.search(r"\berror(?::|\()|sorryAx", diagnostic),
```

**Defect:** The regex `\berror(?::|\()` matches `error:` and `error(` but not bare `error` at end-of-line, `ERROR`, `Error`, or Lean's typical `error: ` format with a space before the colon (which does match, but `Lean error:` without the word boundary won't if preceded by alphanumeric). More critically, `sorryAx` is Lean 4 specific—if upstream uses `sorry` (Lean 3 style) or `admit`, those pass undetected.

The spec says "no-sorry not automatically verified," so partial checking is intentional, but the receipt records `success=True` when sorries may be present under variant spellings.

**Impact:** Evidence marked `success=True` may contain unproven goals. Downstream `verify_acceptance` trusts this boolean.

---

## 5. Security: `within_root` Traversal Check is Correct but `validate_lock_data` Uses It on Untrusted Input (Severity: Medium, Scope: Atomic claims and ownership cleanup)

```python
def within_root(path):
    p = (ROOT / path).resolve()
    p.relative_to(ROOT)  # raises ValueError if outside
    return p
```

**Defect:** This function is correct in isolation. However, `validate_lock_data` calls it on paths from `lock["definition_dependencies"]` and `lock["source"]`, which come from `targets.json`. If `targets.json` is ever written by an untrusted party or corrupted, paths like `../../malicious` resolve safely—but paths containing symlink components on Windows (junction points) may resolve unexpectedly. `Path.resolve()` follows symlinks, so a junction inside `ROOT` pointing outside bypasses the check.

**Impact:** On Windows with NTFS junctions/symlinks, an attacker who controls any file inside `ROOT` can redirect `resolve()` outside the tree after the `relative_to` check passes on the unresolved path.

---

## 6. Correctness: `check()` Double-Validates Locks but Source May Change Between Calls (Severity: Medium, Scope: Source statement lock vs proof changes)

```python
def check(group):
    with exclusive(...), exclusive(...), lease():
        lock, source = validate_locks()       # first validation
        # ... runs gated() twice, potentially minutes apart ...
        validate_locks()                       # second validation
```

**Defect:** The second `validate_locks()` call re-reads `targets.json` from disk. If another process modifies `targets.json` between the first and second call (the `exclusive` lock only protects `operation.lock` and the claim file, not `targets.json`), the second validation fails *after* expensive Lean compilation has already run. The leaf/types receipts are written but the function raises, leaving orphaned evidence with no DAG update.

**Impact:** Wasted compute; inconsistent state where receipts exist but DAG nodes aren't updated.

---

## 7. Correctness: `verify_acceptance` Reads `types` Without Null Guard (Severity: Low-Medium, Scope: Target type check and audit bindings)

```python
def verify_acceptance(evidence):
    # ...
    types = check_record["types"]
    if types["source_sha256"] != lock["type_check_source_sha256"] or \
```

**Defect:** In `check()`, `types` is set to `None` when `leaf["success"]` is False. If a malformed/forged evidence JSON has `check_record["success"] = True` but `check_record["types"] = None`, this line raises `TypeError: 'NoneType' object is not subscriptable` rather than the intended `ValueError`.

**Impact:** Crashes the acceptor instead of cleanly rejecting invalid evidence.

---

## 8. Correctness: Hardcoded Node IDs in Both `check()` and `accept()` (Severity: Low, Scope: Audit bindings)

```python
for ident in ("S1-planar-ball", "S2-actual-CN1-smallball"):
```

**Defect:** These identifiers appear in both functions. If the DAG evolves or the pilot scope changes, these must be updated in lockstep. No validation that these nodes actually exist in the graph before writing verification status. If a node doesn't exist, `read(p)` raises `FileNotFoundError`, which isn't caught by the `except (ValueError, FileExistsError)` handler in `main()`.

**Impact:** Adapter crashes mid-acceptance after evidence is validated but before DAG is updated, leaving inconsistent state.

---

## 9. Security/Cleanup: `exclusive` Finally Block Silently Leaks on Mismatch (Severity: Low, Scope: Atomic claims and ownership cleanup)

```python
finally:
    if path.exists() and read(path).get("token") == token:
        path.unlink()
```

**Defect:** If `read(path)` raises (corrupted JSON, concurrent write), the exception propagates out of `finally`, suppressing the original exception from the `with` body. Additionally, if the token doesn't match (shouldn't happen per the "never take over" contract), the lock file silently persists forever with no logging or ledger entry.

**Impact:** Silent lock leaks; exception masking during cleanup.

---

## Summary Table

| # | Severity | Category | Defect |
|---|----------|----------|--------|
| 1 | High | Concurrency | TOCTOU: lock file exists before JSON written |
| 2 | High | Concurrency | Lease pre-check non-atomic; no compute.lock acquisition |
| 3 | Medium | Lifecycle | Deadline never enforced; hung process = permanent lease |
| 4 | Medium | Correctness | Success regex misses sorry variants |
| 5 | Medium | Security | Windows junction/symlink traversal via resolve() |
| 6 | Medium | Correctness | targets.json unprotected between double-validation |
| 7 | Low-Med | Correctness | TypeError on null types in verify_acceptance |
| 8 | Low | Correctness | Hardcoded node IDs; FileNotFoundError unhandled |
| 9 | Low | Cleanup | Exception in finally suppresses original; silent leak |
