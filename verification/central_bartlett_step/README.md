# General central Bartlett step: checked foundations and open matrix law

This directory rolls forward the same route, not a new hourly research loop.
The actual joint `(r,z,B)` block law is still OPEN. The numeric 3x200000
preflight and real Qoder P1 response are archived; the route decision and
corrections to the response are in notes/CENTRAL_BARTLETT_ROUTE.md.

## Checked fixed-frame foundation

`GaussianComplexFrameExists` has four Codex statements, final frame-2.txt:
complex unit-vector frames, nonzero-vector frames, Gaussian invariance of a
fixed frame and its normalized first-coordinate identity. Basis extension
is pointwise existential. No globally measurable frame has been constructed.

`GaussianComplexMatrixFrame` has eight Codex statements, final
matrix-frame-3.txt: explicit column curry, fixed unitary action as a real
isometry on the entire source, exact sqrt2 coordinate conversion, measurable
matrix action, **full actual central Gaussian matrix law** invariance and
pointwise Gram invariance. These are not scalar-energy surrogates.

All twelve print only propext/Classical.choice/Quot.sound, no placeholders or
toolchain changes. Three failed checks (frame-1; matrix-frame-1/2) are retained,
including exact real-linear coercion rewriting and complex conjugation spelling
errors; they are not accepted proof evidence. The final explicit real isometry
and star normalizations resolve the errors without changing the statements.

Fixed-seed unitary/phase/Gram algebra controls in four dimensions passed.
Numeric controls do not prove the generic statements or a measurable selector.
The actual block-step Monte Carlo controls likewise do not establish a matrix
law from its trace/logdet marginals.

## Review and audit

Qoder/Qwen3.8-Max's real p4-frame response covers exactly the two final sources
and 79 lines of prior support. It found no blocking issue; its scalar-coercion
maintenance observation is already addressed by the explicit real-isometry
map_smul. It did not independently compile or certify human semantics.
[需人工审查] Coordinate/variance/model conventions and future fixed-fiber use.

Reproduce bindings without another bespoke audit program:
`tools/verification/audit_lean_bundle.py --spec verification/central_bartlett_step/frame-spec.json --output verification/central_bartlett_step/frame-audit.json`.
This general auditor checks leaf logs, all public printed names, source and
compiled/dependency hashes, controls and exact supplied review snapshots.
It does not run a full build or human review. Frozen paper/release unchanged.

Further actual row/column block transport is being developed separately;
compiler attempts alone are not acceptance. The complete joint residual-Gram
law, matrix Jacobian and actual general Wishart density/G2 are not claimed.
