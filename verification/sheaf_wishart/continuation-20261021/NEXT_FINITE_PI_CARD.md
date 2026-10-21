# Active next card: finite planar Gaussian polynomial logs

User renewed continuation2026-10-21. Fixed hour2026-10-20 remains CLOSED.
Measure is explicitly pi Fin n stdGaussian C, complex second moment2. Targets are
negative-part L1 and absolute-log L1 for every deterministic MvPolynomial Fin n C.
All-zero polynomial is allowed only for totalized Real.log0=0; nonzeroAE is a
separate theorem with P!=0. No uniform bound over all coefficient choices claimed.

21 fixed-seed200000-sample controls n1..6 and a coefficient-dependent example PASS;
known Gaussian affine/product references and wrongvariance controls included.
Numerics are not proof.

Qoder P1 real response correctly highlights coefficient-zero fibers/product transport,
but incorrectly calls a uniform degree bound missing: pinned Polynomial.natDegree_map_le
already gives it everywhere with D=q.natDegree, without nonzero/AE hypotheses.
No redundant lemma is created to satisfy that warning. The accepted bivariate proof
already uses it. Empty product probability supplies constant integrability directly;
no new identification with Unit/pure is required for that proof.

Lean target headers locked before first check. Finite coordinate splitting uses
measurePreserving_piFinSuccAbove followed by measurePreserving_swap. The nonzeroAE
induction precedes the negative-log induction; leading-coefficient L1 comes from IH.
An independent literal type checker and final-source Qoder P4 are required for acceptance.

[需人工审查] Product transport/Fubini/nullsets/normalization. ProperCN1 scaling and
the pseudoDet spectral comparison needed for singular Wishart offsets remain OPEN.
Linux work copy uses native filesystem for indexing; kernel evidence remains through
the existing Windows serial gate until the Linux gate/toolchain are separately prepared.
