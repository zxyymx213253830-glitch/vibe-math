# SHEAF Windows / Linux comparison

2026-10-21: user authorized a trial and comparison. Linux is NOT_RUN. The current
process is not a Windows administrator. `wsl --status` exits50 and reports WSL
is not installed. Both the documented distribution install command and bare
`wsl --install` exited1 immediately with the same installation message. No Linux
distribution, WSL component, or reboot was started. No administrator prompt was
bypassed. Administrator installation/reboot is the pending user action.

Official installation reference: https://learn.microsoft.com/en-us/windows/wsl/install

## Completed Windows baseline

`experiments/sheaf_platform_benchmark.py` snapshots exact bytes of project Lean
sources, DAG nodes, pinned upstream lexer/scheduler, configuration and dependency
locks. It does not invoke Lean or models, alter project targets or accept proofs.
Snapshot: `.tools/sheaf-platform-benchmark-20261021/snapshot` (381 files).
Tracked `verification/sheaf_platform_benchmark/input-manifest.json` binds these
bytes. The snapshot must be copied verbatim, not recreated from a changed checkout.

Results: `verification/sheaf_platform_benchmark/windows-20261021.json`.
Six separate UTF8 Python processes; the first is reported separately, followed by
five samples for the warm median. The first run is NOT an OS-cold-cache test.
Known lexer/dependency-graph controls pass. All six output hashes match.

| Work | Windows warm median | Linux |
| --- | ---: | --- |
| Whole index/DAG worker including Python startup | 1.0033 s | NOT_RUN |
| Source index: 351 modules, 2152 lexical declaration names | 0.8983 s | NOT_RUN |
| DAG: 24 nodes | 0.00345 s | NOT_RUN |
| Lean kernel compilation | NOT_RUN | NOT_RUN |
| Model proof generation / concurrent landing | NOT_RUN | NOT_RUN |

Lexical declaration counts are not verified theorem counts. Timings describe this
small current DAG and current machine only. No speedup ratio can yet be calculated.
Python version/build and filesystem placement must be recorded as confounds.
This baseline does not measure the complete native Windows acceptance adapter.

## Resume when WSL is ready

1. From an administrator PowerShell, install Ubuntu using `wsl --install -d Ubuntu`.
   User saves work and reboots if Windows requests it; then finishes first launch.
2. Copy the existing snapshot and exact benchmark script into the Linux home
   filesystem. Initially measure there, rather than silently comparing different
   source data. A second `/mnt/d` run can isolate filesystem placement as a factor.
3. Run the exact same script with UTF8 mode and six repeats:

   `python3 -X utf8 sheaf_platform_benchmark.py run --snapshot snapshot --output linux-home.json`

4. Compare result/input/script hashes before timing ratios:

   `python3 compare_sheaf_platform_results.py windows-20261021.json linux-home.json`

5. Only after this stage, prepare an isolated Linux Lean environment with the exact
   pinned `leanprover/lean4:v4.35.0-rc2` and lake-manifest revisions. Record dependency
   preparation separately from repeated checks. Linux compilation requires a
   reviewed portable equivalent of the existing serial compute gate; the current
   helper hardcodes Windows executable paths and process flags. Do not invoke Lean
   directly to evade that gate. Do not reuse Windows timings as Linux measurements.
6. A proof-throughput trial needs independent bounded tasks, identical locked
   statements, explicit model/version/call budgets and the same acceptance rules.
   OS microbenchmarks cannot establish a formalization speedup.

Research hour remains closed; heartbeat remains PAUSED. The prior seven bivariate
declarations are still pending final audit/native acceptance, unchanged by this
benchmark. No mathematics claims or frozen publication artifacts were updated.
