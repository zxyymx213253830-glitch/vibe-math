# Local SHEAF contract

Follow the repository-root AGENTS.md and the user's instructions first. This is a bounded Windows adaptation of pinned frenzymath/SHEAF, not a replacement for those rules.
Read GOAL.md, SETUP.md and coord/STATE.md. Use tools/sheaf.py status/queue/check/accept.
Only work on target-reachable nodes. Atomic claims prevent duplicate task work. Never steal/delete live claims or the shared Lean compute.lock.
All Lean checks MUST pass through tools/deepseek_prover/collaborative_check.py using the existing central session and fresh-project-library. No direct Lean/lake/build scripts.
The coordinator owns compilation and landing. A proof-only edit is allowed while its task is claimed and no check is active; changes to locked statement headers or imported definitions require an explicit new target-lock review, never auto-relock.
Numeric controls precede new proof work. Keep final exact-source P4 from Qoder/different model family and a written issue resolution. Do not treat model agreement as mathematical approval.
Acceptance requires current source/olean/log/review/type-check/audit bindings. A file without sorry is not automatically proved. No new axioms, unsafe or native_decide.
Preserve unknown drafts and frozen publication files. Commit runnable milestones locally; no remote push.
Do not start a recurring automation or indefinite worker loop. A request to continue authorizes one bounded queue operation; status never starts a worker.
