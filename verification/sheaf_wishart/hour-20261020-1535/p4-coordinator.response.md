## P4 Adversarial Review: Concrete Issues

### 1. Incorrect Acceptance: `--lock` Validates Against Wrong Manifest in `status`/`queue`

**Severity:** High (Incorrect acceptance of stale/wrong queue state)

In `main()`, when `args.command` is `"status"` or `"queue"`, the code calls `refresh()` *before* validating `args.lock`:

```python
if args.command in {"status", "queue"}:
    rows = refresh()          # Uses default lock internally via graph() -> dq.load()
    validate_locks(args.lock) # Validates separate manifest AFTER queue built
```

`refresh()` calls `graph()` which calls `dq.load()`, which loads the DAG based on the **original/default** pilot configuration. The subsequent `validate_locks(args.lock)` validates the new manifest but doesn't rebuild the queue against it. The printed queue status and stale-evidence warnings therefore reflect the **original** pilot's state, not the `--lock` module's state. This accidentally reports success/staleness for the wrong module.

**Fix:** Call `validate_locks(args.lock)` before `refresh()`, and ensure `refresh()`/`graph()` parameterize the DAG source when `--lock` differs from default.

---

### 2. Incorrect Acceptance: `check()` Re-validates Lock But Not Source Text After Initial Read

**Severity:** Medium (Failed/stale source acceptance window)

In `check()`:

```python
lock, source = validate_locks(lock_path)  # source_text=None, reads from disk
# ... exclusive locks acquired ...
lock, source = validate_locks(lock_path)  # Re-validates, still source_text=None
nodes = pilot_nodes(lock)
locked_hash = sha(lock_file)
tag = ...
leaf = gated(source, lock["module"], tag + "-leaf")
```

The second `validate_locks` re-reads the lock file and source from disk after acquiring exclusive locks. However, `gated()` computes `before = sha(source)` at invocation time. Between the second validation and `gated()` starting, there's no atomic guarantee the source file hasn't changed if another process held a prior claim that expired. The final acceptance check `sha(source) != leaf["source_sha256"]` catches post-gate drift, but the **initial** hash passed to `gated` could already be stale relative to what was validated. This is conservative refusal territory currently, but the redundant double-validation gives false confidence—it doesn't narrow the TOCTOU window, it just repeats it.

---

### 3. Incorrect Acceptance: `verify_acceptance` Trusts `evidence.get("target_lock")` Without Binding It to the Check Record

**Severity:** High (Validates against wrong original manifest/checker)

```python
def verify_acceptance(evidence):
    lock_file = target_lock_path(evidence.get("target_lock"))
    lock, source = validate_locks(evidence.get("target_lock"))
    check_record = read(within_root(evidence["check"]))
    if not check_record.get("success") or check_record["source_sha256"] != sha(source):
        raise ValueError("Failed/stale source check")
    if check_record["target_lock_sha256"] != sha(lock_file):
        raise ValueError("Stale target lock")
```

The evidence JSON's `target_lock` field is optional (defaults to original). An attacker or misconfigured tool can submit an evidence bundle where:
- `evidence["check"]` points to a valid check record created under **manifest A**
- `evidence["target_lock"]` points to **manifest B**

The check `check_record["target_lock_sha256"] != sha(lock_file)` correctly fails if they don't match. **However**, if manifests A and B happen to share the same SHA256 (collision or copy), all downstream validation uses manifest B's statements/module while the check was performed against A. More critically: the checker source path `lock.get("type_check_source", ...)` is resolved from the **evidence-provided** lock, not from the lock actually used during `check()`. If the evidence omits `target_lock` (defaulting to original) but the check was run with `--lock custom`, the validation passes against the wrong checker hash.

**Missing check:** `verify_acceptance` never confirms that the `target_lock` used during `check()` matches the one referenced in evidence. The check record stores `target_lock_sha256` but not the path; path reconstruction is ambiguous.

---

### 4. Old Pilot Compatibility: `complete_statement` Rejects Valid Equation/Where Syntax That Original Pilot Accepted

**Severity:** Medium (Breaks existing verified nodes)

```python
raise ValueError("Unsupported target syntax: expected top-level proof :=")
```

The docstring acknowledges this intentionally fails closed. However, `verification_current()` calls `verify_acceptance()` which calls `validate_lock_data()` which calls `statements()` → `complete_statement()`. If any **originally accepted** pilot node used equation/where syntax (valid Lean 4), re-validation now throws `ValueError`, marking previously verified nodes as stale. This isn't just conservative refusal—it retroactively invalidates the original pilot lock if the lock contained such syntax. The lock's `statements` dict was presumably built with upstream's permissive parser; local re-parsing now disagrees.

**Check required:** Confirm the original pilot lock (`locks/targets.json`) contains zero equation/where statements. If it does, `validate_lock_data` will never pass, and the entire original pilot is permanently unverifiable.

---

### 5. Failed/Stale Source Acceptance: `accept()` Doesn't Re-validate After `verify_acceptance` Returns

**Severity:** Low-Medium (TOCTOU between verification and DAG write)

```python
def accept(path, group):
    with exclusive(PROJECT / "coord/operation.lock", group):
        graph()
        evidence = read(within_root(path))
        source = verify_acceptance(evidence)  # Validates everything
        lock, _ = validate_locks(evidence.get("target_lock"))
        for ident in (node["id"] for node in pilot_nodes(lock)):
            p = PROJECT / "dag/nodes" / (ident + ".json")
            node = read(p)
            node["verification"] = dict(status="verified", evidence=path, source_sha256=sha(source))
            write(p, node)
```

`sha(source)` is computed at write time, not atomically captured after `verify_acceptance`. The exclusive operation lock prevents concurrent coordinators but not out-of-band file modifications. More importantly: `pilot_nodes(lock)` re-calls `graph().live` which re-parses the DAG. If the DAG changed between `verify_acceptance` reading the check record's node IDs and this call, `pilot_nodes` might update different nodes than were checked. The check record stores node relationships implicitly through `lock["statements"]`, but `graph().live` is the ground truth for IDs—these can diverge if a refresh occurred mid-flight.

---

### 6. Conservative Refusal (Not a Bug, But Documented): `lease()` Unconditionally Blocks on ACTIVE Stage

**Severity:** Informational

```python
if state.get("stage", "").startswith("ACTIVE"):
    raise ValueError("Another active coordinator lease is recorded...")
```

As specified in the requirements, the adapter invokes the gated helper directly rather than using check+lease. However, `check()` itself calls `lease()`. If a prior bounded check crashed without cleanup, `stage` remains `ACTIVE_*` and no new check can start. The requirement states "missing live-lock recovery intentionally fails closed"—this is correct behavior, but the error message ("inspect ownership") doesn't distinguish between "another process is actively running" vs "prior process crashed holding stale lease." Operators cannot safely clear this without manual state.json inspection.

---

### 7. Incorrect Acceptance: Facade Module Name Hardcoded but Path Derived Separately

**Severity:** Low

```python
if facade.get("gated_helper_exit_code") != 0 or facade.get("module") != "JinWishartFormalization":
    raise ValueError("No successful main facade check")
# ...
if facade.get("source_sha256") != sha(LEAN / "JinWishartFormalization.lean") or \
```

The facade check hardcodes `"JinWishartFormalization"` regardless of which `--lock` manifest is active. If a new queue milestone targets a different root module, the facade receipt will always fail validation. Conversely, if the facade receipt was generated for the original pilot but submitted with a `--lock` custom evidence bundle, this check incorrectly passes (wrong module accepted).

---

### Summary Table

| # | Type | Issue | Impact |
|---|------|-------|--------|
| 1 | Incorrect acceptance | `status`/`queue` ignores `--lock` for queue generation | Reports wrong module's state |
| 2 | Conservative refusal | Double `validate_locks` doesn't narrow TOCTOU | False confidence, no actual safety gain |
| 3 | Incorrect acceptance | Evidence `target_lock` not bound to check-time lock path | Validates against wrong checker/statements |
| 4 | Old pilot compat | `complete_statement` rejects syntax original pilot may have accepted | Retroactive invalidation of verified nodes |
| 5 | Stale source | DAG node IDs re-resolved after verification | Could mark wrong nodes as verified |
| 6 | Conservative refusal | `lease()` blocks indistinguishably on stale vs active | Operational ambiguity |
| 7 | Incorrect acceptance | Facade hardcoded to original pilot module | New `--lock` milestones always fail or wrongly pass |

**Critical path for onehour16:35:52UTC hardstop:** Issues #1, #3, and #4 can cause incorrect acceptance or permanent lockout of the original pilot. Recommend gating `accept` on explicit confirmation that `evidence["target_lock"]` matches the check record's originating lock path, and verifying the original `targets.json` contains no equation/where syntax before hardstop.
