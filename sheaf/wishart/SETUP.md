# SHEAF Wishart Windows pilot

- Existing Lean project: `D:/vibe math/theory/jin_wishart_formalization`.
- Lean pinned: leanprover/lean4:v4.35.0-rc2; existing Mathlib lock unchanged.
- User authorization: install/adapt SHEAF and operate it; bounded scalar-smallball pilot.
- Coordinator: current Codex; proof workers one task at a time; Qoder CLI bounded P4.
- Compile concurrency: exactly1 through existing collaborative_check.py and central compute.lock.
- No automatic purchases, quota reset, account switch, remote push, background heartbeat, or toolchain upgrade.
- Target statements locked before proof check. Compiler type equality is a local check, not a run of leanprover/comparator.
- Windows adaptation uses native Python. Upstream Bash/tmux/fcntl workflow is not installed or started.
- Accepted sources contain no sorry/admit/new axioms. Source-level DAG status requires compile/review/audit evidence even if no sorry occurs.
- Human measure/Fubini/variance/model review remains REQUIRED.
