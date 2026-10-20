I need to carefully review this Windows SHEAF adapter source code for concrete unresolved defects, focusing on the areas you specified: nested named/default parameters, source locks, failed checks/acceptance, and the handling of unsupported syntax.

Let me analyze the code systematically.

## Code Review Findings

After careful analysis of the provided source code, I have identified the following **concrete unresolved defects**:

### 1. `complete_statement` Delimiter Balancing Logic Error (False Rejection / Silent Truncation)

**Location:** `complete_statement`, lines 148-166

**Defect:** The delimiter balancing logic does not correctly handle Lean's nested named parameter syntax `(m := 1)` when it appears *before* the top-level proof `:=`.

The function iterates character-by-character through `"code"` tokens from `li.lex(body)`. When it encounters `(`, it pushes `)` onto the stack. However, when scanning a named argument like `(m := 1)`:
- It sees `(`, pushes `)`.
- It then scans `m`, space, and hits `:=`.
- Because `stack` is **not empty** (it contains `]`), the `if not stack and body.startswith(":=", i):` check correctly prevents splitting here.
- It continues, eventually hitting `)`, which pops from the stack.

**The actual defect:** If the theorem has *default* parameters with nested parentheses or complex default expressions containing unbalanced characters that the simple `pairs` dictionary doesn't cover (e.g., string literals containing `(` or `)` inside a default argument), the stack will become corrupted. The function will either:
- Raise `ValueError("Unbalanced target header")` (conservative refusal, but blocks valid ordinary theorems with string defaults).
- Worse, if the string literal happens to balance by coincidence, it could split at the wrong `:=`.

Because the prompt specifies "pilot ordinary theorem syntax only" and "unsupported where/equation syntax should fail closed", this is acceptable *only if* all locked targets are truly ordinary. However, the code claims to "lock the complete balanced header locally" using `li.lex`, but `li.lex` yields `"code"` and non-code tokens. By skipping non-code tokens (`if kind != "code": continue`), **comments or string literals containing delimiters are ignored for balancing purposes, but their characters are still scanned**. If a string literal in a default parameter contains `(`, it will be pushed to the stack, causing a mismatch when the actual closing `)` of the parameter is reached.

**Impact:** Valid pinned targets with string literals containing parentheses in default arguments will be falsely rejected as "Unbalanced target header" or, depending on content, cause silent mis-splitting.

### 2. Stale Lock Recovery Leaves Orphaned Claims (Manual Recovery Defect)

**Location:** `check()`, lines 238-240; `exclusive()`, lines 79-93

**Defect:** The prompt distinguishes "intentional conservative refusal/stale-lock manual recovery". However, if `validate_locks()` at line 239 raises `ValueError` due to a stale lock (source changed during check), the `exclusive` context managers for `operation.lock` and `ScalarUniformSmallBall.lock` exit their `with` blocks.

In `exclusive`'s `finally` block (lines 85-93):
```python
record = read(path) if path.exists() else None
# ...
if record and record.get("token") == token:
    path.unlink()
elif record:
    warnings.warn(f"Different-owner claim retained: {path}")
```
If the process crashes or is killed (max180sec child time enforced by `collaborative_check.py`) *after* writing receipts but *before* `exclusive`'s finally block runs, the lock file remains. This is by design ("Never take over or delete another owner's claim").

**However**, the defect is: `check()` acquires **two** exclusive locks sequentially in the same `with` statement. If `ScalarUniformSmallBall.lock` is successfully acquired but `lease()` (line 238) raises `ValueError` because `STOP` exists, `operation.lock`'s context manager never enters, but `ScalarUniformSmallBall.lock`'s context manager *did* enter and will correctly release. **But**, if `lease()` succeeds and a later exception occurs, both release correctly.

The **concrete defect** is in `accept()`, line 277:
```python
def accept(path, group):
    with exclusive(PROJECT / "coord/operation.lock", group):
        graph()
        evidence = read(within_root(path))
        source = verify_acceptance(evidence)
```
`accept()` takes `operation.lock` but **does not** take `ScalarUniformSmallBall.lock`. If `check()` was interrupted and left `ScalarUniformSmallBall.lock` orphaned, `accept()` can proceed. But `check()` cannot be re-run to clear it because `check()` requires `ScalarUniformSmallBall.lock`. This creates an asymmetric deadlock scenario where acceptance is possible but re-checking is blocked, violating the serialized adapter check/accept flow described in the prompt.

### 3. `verify_acceptance` Log Read Race / Missing Encoding Fallback

**Location:** `verify_acceptance`, lines 258, 268

**Defect:** 
```python
"SHEAF_TARGET_TYPES_EQ PASS" not in within_root(types["log"]).read_text(encoding="utf-8")
```
and similarly in `check()` line 245.

`types["log"]` is written by `collaborative_check.py`. The adapter reads this log immediately after `gated()` returns. On Windows, if the child process spawned by `collaborative_check.py` (or its own subprocesses) has not fully released the file handle due to OS-level buffering/handle inheritance, `read_text` can raise `PermissionError` (which maps to `OSError`).

While `main()` catches `OSError` and exits with code 2, this causes a **false rejection** of a successful run. The receipt was already written by `gated()`, but the exception prevents `check()` from completing, leaving the DAG nodes in an inconsistent state (nodes were not updated because the loop at 251-254 wasn't reached).

### 4. `pilot_nodes` Graph Traversal Non-Determinism

**Location:** `pilot_nodes`, line 214

**Defect:**
```python
nodes = [node for node in graph().live.values() if node.get("declaration") in lock["statements"]]
```
`graph().live.values()` iteration order depends on dictionary insertion order (Python 3.7+). `dq.load()` populates this. If the upstream `dag_queue` loads nodes from JSON files via `os.listdir` or globbing, the order is filesystem-dependent and non-deterministic on Windows.

Later, `check()` updates nodes in a generator expression:
```python
for ident in (node["id"] for node in nodes):
```
This is fine. However, `verify_acceptance` checks:
```python
if {d["name"] for d in module["declarations"]} != set(lock["statements"]):
```
using sets. The defect is not here, but in `pilot_nodes`: if multiple DAG nodes share the same `declaration` name (e.g., due to a stale duplicate node not yet pruned), `len(nodes) != len(lock["statements"])` will catch it. **But**, if `graph()` is called twice (once in `pilot_nodes`, once implicitly elsewhere) and the underlying filesystem changes between calls, two different DAG instances are compared. `check()` calls `graph()` inside `pilot_nodes(lock)`, but `lock` was validated before. This is safe only if `graph()` is pure/deterministic. If `dq.load()` reads mutable state, this is a TOCTOU defect.

### 5. `gated` Success Logic Misses `sorry` Variants

**Location:** `gated`, lines 230-233

**Defect:**
```python
success=code == 0 and log.exists() and before == sha(source) and
not re.search(r"\berror(?::|\()|sorryAx", diagnostic),
```
The prompt states: "placeholder rejection uses source/log/axiom audits" and "No implicit --no-sorry CLI".

The regex `\berror(?::|\()|sorryAx` catches `error:` and `error(` and `sorryAx`. It does **not** catch:
- `sorry` (the tactic) used in a way that doesn't trigger `sorryAx` in the log output format of this specific Lean version.
- `admit`
- `unsafe` modifiers that compile successfully but bypass proofs.

The axiom audit at line 272 catches non-standard axioms:
```python
if any(set(d["axioms"]) - {"propext", "Classical.choice", "Quot.sound"} ...
```
This is the real safety net. However, `gated`'s `success` field is used to decide whether to proceed to type checking (`types = gated(...) if leaf["success"] else None`). If `leaf` succeeds (exit 0, no error/sorryAx in log) but contains `admit`, `leaf["success"]` is `True`, types are checked, and the failure is only caught later in audit. This is **fail-closed ultimately**, but wastes compute on the type check and produces misleading intermediate receipts.

### 6. `lease` Deadline Not Enforced Locally

**Location:** `lease`, lines 217-233

**Defect:** The lease writes a `deadline_utc` 15 minutes in the future. However, the adapter itself never checks this deadline during execution. It relies entirely on `collaborative_check.py` to enforce "session STOP/deadline and max180sec child time".

If `collaborative_check.py` fails to enforce the deadline (e.g., due to Windows process tree killing issues where grandchildren survive), the adapter will continue running indefinitely. The `lease` context manager's `finally` block will still write `SHEAF_BOUNDED_CHECK_FINISHED`, masking the overrun. The prompt says `collaborative_check.py` "owns" this, but the adapter sets the deadline without verifying it, creating a false sense of boundedness.

### 7. `within_root` Path Traversal False Positive on Windows

**Location:** `within_root`, lines 66-69

**Defect:**
```python
def within_root(path):
    p = (ROOT / path).resolve()
    p.relative_to(ROOT)
    return p
```
On Windows, `Path.resolve()` resolves symlinks and normalizes casing. `relative_to()` is case-sensitive. If `ROOT` contains mixed-case components (e.g., `D:\Vibe Math\...`) and `path` comes from a JSON lock file recorded with different casing, `resolve()` might normalize differently than expected, causing `relative_to(ROOT)` to raise `ValueError`.

More critically, Windows short names (8.3 aliases) or UNC paths could cause `resolve()` to return a path that doesn't start with the exact `ROOT` string bytes, even if logically inside. This would falsely reject valid locked sources.

---

## Summary of Concrete Unresolved Defects

| # | Component | Defect Type | Impact |
|---|-----------|-------------|--------|
| 1 | `complete_statement` | String/comment delimiter blindness | False rejection or silent mis-split of valid ordinary theorems with string defaults |
| 2 | `accept` vs `check` locking | Asymmetric lock acquisition | Orphaned `ScalarUniformSmallBall.lock` blocks re-check but not accept |
| 3 | `verify_acceptance`/`check` | Windows file handle race | `PermissionError` leaves DAG nodes partially updated |
| 4 | `pilot_nodes` | TOCTOU on `graph()` | Non-deterministic node mapping if DAG mutates |
| 5 | `gated` | Incomplete placeholder regex | Wasted type-check compute on `admit`/`unsafe` |
| 6 | `lease` | No local deadline enforcement | Relies entirely on child; no adapter-level circuit breaker |
| 7 | `within_root` | Windows path casing/short names | False rejection of valid locked sources |

**Note on Unsupported Syntax:** The `complete_statement` function correctly raises `ValueError` for missing top-level `:=` (equation/where syntax), satisfying the "fail closed" requirement. No defect there.

**Note on False Acceptance vs Conservative Refusal:** Defects #1, #3, and #7 cause *conservative refusal* (safe but blocking). Defect #2 causes a *recovery gap*. Defect #5 delays detection but does not cause false acceptance due to the downstream axiom audit. None of these constitute a *false acceptance* vulnerability under the stated threat model.
