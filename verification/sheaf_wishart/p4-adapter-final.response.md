I'll review the source directly for concrete failure scenarios, distinguishing incorrect acceptance from conservative rejection.

## Remaining Concrete Failure Scenarios

### 1. Incorrect Acceptance Risks (Soundness Bugs)

**A. `verify_acceptance` facade log hash race**
Lines 213-215: `facade_log` is derived from `facade_path` by string manipulation *after* `facade_path` was resolved via `within_root(evidence["facade_receipt"])`. The log hash is checked against `sha(facade_log)`, but the facade receipt's `log_sha256` field is never compared to the actual log content at receipt creation time in `gated()`. If a prior run wrote a receipt with a missing/corrupted log that later got created/overwritten by something else, `verify_acceptance` would accept based on the current file content matching the old receipt's claim, even though `gated()` only records `log_sha256` if the log exists at gate time. **However**, `gated()` does set `log_sha256=sha(log) if log.exists() else None`, so this is actually safe — the risk is conservative (see below).

**B. `check_record["leaf"]["source"]` comparison is path-string, not content-hash**
Line 189: `check_record["leaf"]["source"] != lock["source"]` compares the `rel(source)` string from `gated()` against `lock["source"]`. If the lock file contains a logically equivalent but textually different relative path (e.g., `./foo` vs `foo`), this raises ValueError incorrectly. Conversely, if two distinct files somehow map to the same `rel()` output (impossible given `relative_to(ROOT)`), it would be unsound. This is correct but brittle to lock-file formatting.

**C. No validation that `evidence["check"]` points to a check produced by THIS adapter**
Line 175: `check_record = read(within_root(evidence["check"]))` reads an arbitrary user-supplied path. The record has no cryptographic binding to this adapter's identity beyond structural checks. A crafted JSON file with correct hashes and `"success": true` could pass if the attacker also controls the referenced log/receipt files. This is acceptable per the threat model ("local files are owned project configuration, not adversarial"), but worth noting: this is manual recovery trust, not automated soundness.

### 2. Conservative Rejection / Manual Recovery Scenarios (Not Soundness Bugs)

**A. `exclusive()` refuses to clean expired foreign locks**
Lines 68-70: If another process crashed holding `operation.lock` or a claim lock, the adapter warns and retains it forever. No timeout/recovery mechanism exists. This is intentional per the docstring but means manual deletion is the ONLY recovery path. Not a bug; a design constraint requiring human intervention.

**B. `lease()` rejects on stale STOP/compute.lock/CODEX_REVIEW from dead processes**
Lines 130-131: Checks `.exists()` without validating liveness of the owning process. A crashed Codex session leaves these files permanently blocking the adapter. Again, intentional ("inspect ownership; adapter will not remove it") but creates unavoidable manual recovery.

**C. `gated()` pre-existence check is TOCTOU**
Lines 147-148: `if log.exists() or receipt.exists(): raise ValueError("Refusing to overwrite evidence")` then proceeds to write. Between check and `subprocess.run`, another process could create these files. The subsequent `write(receipt, result)` uses atomic `os.replace` via `write()`, so corruption is impossible, but the subprocess runs wastefully before the receipt write reveals the collision. Conservative failure, not acceptance.

**D. Stale-evidence requeue doesn't invalidate `verification_current` cache within single `refresh()` call**
Lines 108-109: `queue_data` calls `verification_current(node)` which calls `verify_acceptance`. If `verify_acceptance` fails due to a transient file read error (OSError), it returns `False`, causing the node to be requeued as `stale-evidence`. On the next `refresh()` call (e.g., immediate re-run), if the transient error resolves, it may flip back. This oscillation is conservative — it never incorrectly marks stale evidence as current.

**E. Source SHA double-check in `check()` can reject valid runs**
Lines 161-162: `sha(source) != leaf["source_sha256"]` compares post-compilation source hash against the hash recorded inside `gated()`. But `gated()` already records `source_sha256=sha(source)` after compilation (line 155). So this line 162 check is comparing `sha(source)` now vs `sha(source)` at gated-return time. If the source file changes between `gated()` return and line 162, this correctly fails closed. However, `leaf["source_sha256_before"]` already captured the pre-compilation hash; the redundancy is defensive, not buggy.

**F. Missing receipt guard in `verify_acceptance` is overly strict on structure**
Lines 185-186: `not all(isinstance(check_record.get(part), dict) for part in ("leaf", "types"))` rejects if `types` is `None` (which `check()` sets when `leaf["success"]` is False, line 160). But `verify_acceptance` is only called from `accept()` and `verification_current()`. In `accept()`, the evidence must have `success=True` (line 176), meaning `types` was populated. In `verification_current()`, exceptions are caught (line 231). So this is reachable-conservative, not a false-accept risk.

### 3. Edge Cases That Are Neither (Correct Behavior)

**A. `graph()` validates deps exist but not that they're in `g.dist`**
Lines 83-84: Missing dependencies raise ValueError. But nodes outside `g.dist` are silently deferred (lines 119-120). This is correct: structural integrity vs. scheduling scope separation.

**B. `pilot_nodes` requires exact 1:1 mapping**
Lines 137-139: If the DAG has duplicate declaration names or the lock references declarations not in the DAG, it fails. This prevents partial verification of wrong targets. Correct fail-closed.

**C. Axiom check allows exactly `{"propext", "Classical.choice", "Quot.sound"}`**
Lines 207-208: Any other axiom (including `sorryAx`) causes rejection. Since `collaborative_check.py` runs Lean with `--no-sorry` semantics and the type-comparison uses `isDefEq`, this is the correct final gate. The `sorryAx` regex in `gated()` (line 156) is defense-in-depth.

### Summary Table

| Scenario | Type | Root Cause | Impact |
|----------|------|------------|--------|
| Crafted evidence JSON | Incorrect acceptance (if trusted) | No adapter signature on receipts | Mitigated by local/non-adversarial threat model |
| Expired foreign locks | Conservative rejection | `exclusive()` never cleans | Manual recovery required |
| Dead-session STOP/locks | Conservative rejection | `lease()` checks existence only | Manual recovery required |
| Facade log path derivation | Safe | String manipulation matches `gated()` output | No issue |
| Transient OSError in `verification_current` | Conservative rejection | Exception → `False` | Self-heals on retry |
| `types=None` in failed check | Conservative rejection | Structure check rejects `None` | Only reachable on already-failed paths |

**Bottom line**: No remaining scenario produces incorrect acceptance under the stated threat model. All identified edge cases fail closed. The primary operational cost is manual recovery from stale locks/evidence, which is architecturally intentional.
