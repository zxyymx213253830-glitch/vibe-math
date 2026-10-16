# Reproducing the working manuscript and proofs

The manuscript is `main.tex`. It has an embedded bibliography, no local input
files, and no external figures. From an environment with a conventional TeX
distribution, run `pdflatex -interaction=nonstopmode -halt-on-error main.tex`
twice. The repository delivery PDF is under `output/pdf/`.

## Pinned Lean project

The Lean project is `theory/jin_wishart_formalization`:

- `lean-toolchain`: `leanprover/lean4:v4.35.0-rc2`.
- mathlib revision: `e18afff334217588afc719a8b707b00d90521064`.
- Transitive revisions: the committed `lake-manifest.json`.

Do not run `lake update` for replication. Obtain the exact dependencies and
their matching cached artifacts, then run `lake build` in the project directory
for a conventional Lake build. The publication report does **not** claim that
this command has been executed or that mathlib was rebuilt from source.

## Fresh project-source verification actually used here

`verification/rebuild_wishart_sources.py` topologically elaborates every project
source, including the aggregate entry, into a new output directory. External
packages use pinned caches; project imports use the fresh directory. Every
command goes through `tools/deepseek_prover/collaborative_check.py` and its
exclusive compute gate, with one Lean worker. It records source SHA256 and
requires the source to remain unchanged during checking.

The helper currently targets the documented Windows workspace paths. On another
machine, configure the constants in `tools/deepseek_prover/hour_runner.py` to the
equivalent project, Python and **same-version** Lean executable paths. Those
machine-local path adjustments do not change theorem sources or dependencies.

For a new run, choose a fresh directory under `.tools/`, create `state.json`
with an ISO8601 UTC `deadline_utc` as a safety bound, then run:

```
D:/miniconda3/python.exe verification/rebuild_wishart_sources.py --session <fresh-directory>
```

Do not reuse a live gate or a prior timed research runner. `--resume` reuses only
successful outputs from this fresh-source run with matching source hashes. Changed
or recompiled dependencies force their dependents to be rechecked. Failed attempt records are
retained. The report is
`verification/WISHART_PUBLICATION_REBUILD.json`; its status, hashes, and method
should be read together. A resumed run is not an independent second reproduction.

The previous report's `started_utc` was reset when resuming. Its approximately
74-second top-level interval described only the last batch, not 164 module
compilations. The original is retained as
`verification/publication_checks/rebuild-52f8899-resumed.json`; historical
per-module durations were not measured and are not reconstructed. Schema 2
records one campaign origin, each batch's compiled/reused counts, and UTC
start/finish plus monotonic wall seconds for every new module check. Wall time
includes helper and gate overhead. The revision uses a new fresh output
directory rather than relabeling the old cached results as new timings.

## Numerical controls

From the repository root:

```
D:/miniconda3/python.exe experiments/two_row_log_rate_outage.py
```

This uses numpy/scipy, seed 20261015, and 200000 actual complex Gaussian samples.
It writes `verification/WISHART_LOG_RATE_OUTAGE.json`. Trace/Gamma,
minimum/exponential, numerical eigenvalue, and event-transform controls are
asserted. Numerical tolerances are controls, not formal confidence guarantees
or proofs. Older rank-one T3 diagnostics remain separate from this experiment.

## Claims, review, and artifact integrity

`claims.json` maps paper claims to exact declaration identifiers and source hashes.
`verification/prepare_wishart_publication.py` checks that these names occur in
their source modules and builds a transitive source manifest and lexical audit.
The expanded `ClaimsCheck.lean` audits every public theorem in all named entry
modules, including the two general-coordinate modules, the Wishart API wrapper,
and explicit local helper bodies. Run `verification/check_publication_axioms.py
--session <campaign-directory>` after the fresh build and final manuscript edit.
Its binding report records source/dependency, compiled olean, audit-source,
actual output-log, toolchain, manifest, and manuscript hashes; it rejects
changes during checking. Regenerate the claims manifest afterward. A changed
manuscript also requires a new binding check, even if no Lean text changes.
Declaration lookup and token scanning do not replace kernel checks; the rebuild
report and scoped model review/human review are separate evidence.

An existing independent WorkBuddy report (Step model family) reviewed the stated
subset and reported no concrete mathematical errors within it. The reviewed
96-source snapshot was rehashed before the current editorial changes; Lean
sources are unchanged. The report, original manifest, manuscript and issue
dispositions are included. This is not a full dependency proof-body or human
review. Fubini/skew-product specifications, model/notation matching and intrinsic
Frobenius volume interpretation remain [需人工审查]. Author: ZHOU XINGYUAN.
Release rights/license and final human mathematical signoff remain separate.

Source hashes are byte-exact. The local review ZIP preserves those bytes;
Git checkout line-ending conversion can change a raw hash without changing the
Lean text. Use the packaged source snapshot when comparing the recorded hashes.

The revised artifact includes `WISHART_WORKFLOW_AUDIT.json` and actual round3
events and review requests/responses. The 38 runner generations, two separate
manual calls, and five P4 requests have distinct denominators. No controlled
model-comparison claim is made. Internal T3 normalization experiments are not
part of this manuscript's claims or numerical evidence package.

## Current acceptance snapshot

The recorded 164-module fresh pass is followed by an incremental 165-module
snapshot: the new HermitianCoordinateMetric and changed aggregate entry were
checked; reused source/output hashes were validated. The new authorization gate
was supplied with `--gate-session .tools/publication-acceptance-20261016`, without
extending the expired research window. The 119-declaration audit and 22-claim
manifest match this snapshot and the final manuscript. Old failed attempts are
retained, including Lean-generated error recovery axioms in failed logs; these
are not accepted proof dependencies. The standalone pending draft was promoted
to the checked project module and is no longer a second unverified source copy.

The earlier read-only Claude invocation returned API 402 and no issue report;
its archived failure is historical and does not negate the subsequently
provided Step report. No new model review is started by these packaging tools.
