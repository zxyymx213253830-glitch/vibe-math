# SHEAF Windows / WSL2 Linux comparison

Current result, 2026-10-21: the index/DAG comparison is COMPLETE. This is not a Lean
compiler, model proof-generation, or end-to-end formalization throughput benchmark.

## Measurements

Same exact script, 381 input files (351 Lean modules and 24 DAG nodes), six separate
UTF8 Python processes per environment. First process reported separately; table
uses medians of the following five. All 18 fresh-run outputs have exactly the same
result SHA256, and known lexer/DAG controls PASS. The 2152 lexical declaration
names are NOT a verified theorem count. No OS cache flush was performed.

| Environment | Worker incl. Python startup | Source index | DAG load/route |
| --- | ---: | ---: | ---: |
| Windows native, D: | 0.9811 s | 0.8838 s | 2.959 ms |
| WSL2 Ubuntu, Linux home filesystem | 0.5387 s | 0.4897 s | 4.049 ms |
| WSL2 Ubuntu, Windows /mnt/d files | 7.9130 s | 7.0627 s | 517.678 ms |

Observed worker ratio: Windows/Linux-home = 1.82.
Linux-home was about 45.1% shorter for this task.
The mounted Windows path was 8.07 times as long as
Windows native, and 14.69 times as long as Linux-home.
DAG-only work is a few milliseconds locally and was not uniformly faster on Linux.

**Confounds:** Windows Python3.14.7 Anaconda/MSVC versus Ubuntu Python3.14.4/GCC;
WSL2 virtualization versus native Windows; filesystem placement; finite small
sample; uncontrolled background load. Thus this is a practical environment
comparison, not an isolated causal measurement of OS alone. No end-to-end
formalization acceleration factor is inferred. A ~0.44-second local saving cannot
by itself establish a major improvement to minute-long proof/model loops.

Recommendation from this measured workload: if continuing in WSL, put its working
copy in the Linux filesystem, not /mnt/d. Microsoft gives the same filesystem
placement guidance: https://learn.microsoft.com/en-us/windows/wsl/filesystems
No project migration was made; only a benchmark snapshot was copied.

## Native compatibility

Ubuntu26.04.1 on WSL2 kernel6.18.54.1; isolated distro name `SheafBenchUbuntu`.
Bash and tmux were already installed. Real cross-process fcntl exclusion and
release control PASS; private tmux session creation/lookup PASS and its owned
server was shut down. First smoke invocation had a Python string-escaping error;
its failed receipt is retained. The corrected smoke source and successful second
receipt are preserved. This does NOT certify the whole upstream autonomous
launcher, landing system or comparator, which remain NOT_RUN.

Existing localhost proxy settings produced a WSL NAT warning. No proxy/auth keys
were copied or changed; Linux model CLI network/login paths remain untested.

## Setup and provenance

WSL runtime was installed by the user, then Windows restarted. Standard Ubuntu
download failed after303.7s with WININET_E_INVALID_SERVER_RESPONSE. Its owned web
retry was stopped after104.8s. A slow direct-source download was also stopped via
its owned tool session; the partial file was never installed. USTC mirror download
completed129.0s (418495746 bytes). Its SHA256 exactly matched the Microsoft WSL
manifest: `48d56724b5c8e60f24893e83e73bbb58c60b3ca22fba3da977075420acd54104`.
Local-image installation took12.76s; snapshot copying took18.32s. These one-time
costs are outside the warm worker timings. First Linux boot/preflight includes
additional setup costs recorded in receipts.

Manifest source: https://raw.githubusercontent.com/microsoft/WSL/master/distributions/DistributionInfo.json
Upstream image: https://releases.ubuntu.com/26.04.1/ubuntu-26.04.1-wsl-amd64.wsl
Mirror: https://mirrors.ustc.edu.cn/ubuntu-releases/26.04.1/ubuntu-26.04.1-wsl-amd64.wsl

Image and distro live under `.tools/sheaf-platform-benchmark-20261021/`; native
snapshot lives at `/root/sheaf-platform-benchmark-20261021`. The native experiment
used explicit `--user root`; no account/password was created or changed. No
unrelated processes or locks were stopped. No persistent tmux experiment server
remains. Distro is installed for future work; it was not unregistered.

## Reproduction and next boundary

- Benchmark: `experiments/sheaf_platform_benchmark.py`; input manifest and each raw
  measurement/receipt: `verification/sheaf_platform_benchmark/`.
- Result matcher: `experiments/compare_sheaf_platform_results.py`. It rejects
  different script/input/output hashes; reports Python version mismatch.
- Same Linux interpreter measured both Linux-home and /mnt/d, so their comparison
  holds Python version constant. Native Windows comparison has the confounds above.
- Read-only index/DAG benchmarking invokes no Lean or model. A future kernel test
  must keep leanprover/lean4:v4.35.0-rc2 and lake-manifest revisions, prepare native
  dependencies separately, and port/review the shared serial compute gate first.
  The current gate hardcodes Windows executable paths and process flags; direct
  Lean invocation must not bypass it. No Linux dependencies/toolchains upgraded.

Research hour remains CLOSED; heartbeat PAUSED. The seven bivariate declarations
remain pending final audit/native acceptance. No frozen publication artifacts or
mathematical claims were changed by this test. Full Lake/mathlib build NOT_RUN.
