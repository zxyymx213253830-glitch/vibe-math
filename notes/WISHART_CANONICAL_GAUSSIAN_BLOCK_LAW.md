# Rectangular proper-Gaussian frame and arbitrary disjoint matrix blocks

Codex proofs in GaussianRectangularFrameLaw, GaussianDisjointMatrixBlockLaw,
and ActualCanonicalNoiseBlockLaw: six printed declarations, not six novel
probability breakthroughs. The generic Gaussian coisometry fact is an
application of the existing characteristic-function theorem; the actual
matrix and joint source statements below are the missing model bridges.

For fixed U:p-by-b with U^H U=I, a central proper-CN1 m-by-p matrix Z satisfies
Z U ~ proper-CN1 m-by-b. The statement is the entire matrix law, including
joint independent entries, not just a covariance identity. Its adjoint-column
version applies any fixed complex isometric embedding's adjoint to every
column. Realification explicitly matches real and complex adjoints, then a
finite-column lift reuses the old Gaussian coisometry theorem. The proper
variance scaling1/sqrt2 is retained in matrixLawCoordinates.

For arbitrary fixed M and arbitrary injective disjoint selectors e,f,
selected full columns have the product of their actual shifted proper-CN1
matrix laws. The analogous full ROW block statement follows by the already
established conjugate-transpose law. The selectors need not exhaust all
rows/columns. The joint-injectivity hypothesis includes both injectivity of
each selector and disjointness of their images. Empty blocks are included.
The proof reuses stdGaussian_disjoint_columnSelections; it does not repeat
its finite Gaussian product construction or assume Wishart independence.

The final same-source theorem keeps the original2mp real Gaussian source:
for fixed row unitary V, fixed U^HU=I, fixed mean M:m-by-b, and disjoint row
selectors, the selected row blocks of V(ZU)+M have exactly the product of
their actual shifted proper-CN1 laws. Neither U nor V depends on the sample.
It does not claim invariance under the non-isometric column equivalence e
from the deterministic canonical construction. That e is a different map.

## Controls and kernel evidence

rectangular_gaussian_frame_control.py seed2026102223:60 shapes/662 exact
controls, including U^HU=I, V^HV=I, real covariance1/2, zero pseudo-covariance,
known E||VZU||_F^2=mb, empty shapes, pointwise vectorization, and negative
missing-sqrt2/conjugation controls. A SymPy unsimplified structural equality
failure is retained; its replacement simplifies exact expressions. A second
slow own process was stopped to avoid expression swell; the final bounded
version caches covariance and passes. Neither rejected run is evidence.

disjoint_gaussian_block_control.py seed2026102224:62 cases/408 exact controls,
including arbitrary fixed complex means, permuted disjoint selectors, empty
blocks, proper component variance and overlap-negative controls. Both sets
are controls only, not proofs of independence or a Gaussian law. Their
source/result/seed bindings are included in the audit.

Seven unsuccessful preliminary rectangular-law source snapshots/logs are
retained. They concern LinearMap versus ContinuousLinearMap adjoints,
semireducible matrix/function map rewrites, finite-sum ordering, and the
fun_prop search on rectangular multiplication. The latter was replaced by
its precise continuous_const.matrix_mul proof; the temporary raised local
heartbeat limit was removed. Final v8 passes at the default limit. The block
law passed first try; the final same-source composition v1 assoc/coercion
rewrite failure is preserved, v2 passes. Only the final unchanged sources,
six literal target types and standard three axioms are accepted.

## Different-family P4 and resolution

Real Qoder Qwen3.8-Max reviewed all three full final sources with tools
disabled. Prompt, receipt, response and snapshots are bound; no follow-up
approval attempt. It retracts its initial variance alarm after following the
source scaling, and identifies one conditional API question: whether the old
complexGaussianMatrixLaw_unitary_invariant accepts an actual complex linear
isometry equivalence and acts identically column-wise. The precise accepted
signature in GaussianComplexMatrixFrame.lean does exactly this:
U:EuclideanSpace C(Fin m) equiv_linear_isometry EuclideanSpace C(Fin m),
map(unitaryActColumns U) of the FULL central matrix law equals that same law.
No Matrix.unitaryGroup conversion or unproved independence premise is used.

The response's phrase variance1/2 per complex entry is imprecise: each REAL
component has variance1/2; E|z|^2=1. The source, exact controls and final
matrix-law statements all use the latter proper-CN1 convention. The review
finds no sum/realification/disjointness gap beyond its resolved signature
question. Scoped P4 is not human approval or independent compilation.

[需人工审查] Actual-source pushforward identities, coordinate normalization,
product measures, subsequent Holder/Fubini/limits and the physical model
remain required. General singular-B positive-minimum inverse thresholds and
Fin quantitative spectrum transport are still OPEN. Frozen publication
artifacts unchanged; full Lake/mathlib and independent Linux kernel NOT_RUN.

The first combined audit rejected missing source_sha256 fields in the new
control JSONs. The rejection record and old scripts/results are retained.
The control runners gained explicit source provenance and were rerun because
those scripts changed;662 and408 results were unchanged. The audit was not
weakened, and no final Lean source/P4 bytes changed for this metadata repair.
