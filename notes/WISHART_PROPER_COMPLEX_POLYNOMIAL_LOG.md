# Proper CN1 polynomial and physical compressed determinant log-L1

2026-10-21 fixed-hour milestone. Every fixed holomorphic complex MvPolynomial on
an arbitrary finite index type has negative-part and absolute totalized real log
integrable under standardComplexPiLaw. Each physical entry has variance1/2 per
REAL coordinate and complex second moment1. Finite-type enumeration and coordinate
scaling are explicitly proved, not inferred from absolute continuity.

Actual physical Gaussian matrix-entry polynomials inherit these L1 properties via
complexMatrixEntries_law. For arbitrary fixed rectangular/singular/zero B,M and
fixed q-by-m L,n-by-q H, det(L*(ZB+M)*H) has negativeLog and absolute-log L1.
This is not an assertion that this determinant is nonzero: zero polynomials and
identically singular compressions use Real.log0=0. Nonzero witness selection and
pseudoDet/positive-eigenvalue-product comparison remain separate.

23 controls seed2026102124,200000samples: scaling evaluation identity, known proper
Gaussian product/affine log moments, square Bartlett logdet references q1..3,
empty dimension/totalized zero and a missing-sqrt2 negative control. AllPASS, not proof.

Ten independent literal type comparisons PASS, both final locked leaf checks real
exit0, standard3 axioms only; facade60 exit0. Proofs Codex. Qoder P1/P4 real raw
responses retained, not independent compilation or human approval.

P4 history/resolutions:
- First full-source call timed out90s, NOT a delivered review.
- Second substantive response lacked upstream definitions and speculated about
  reversed scaling, while confirming the q-by-q dimensions.
- Final follow-up includes the FULL GaussianMatrixPolynomialLaw source and exact
  source/type definitions. It confirms the transport chain and no remaining math
  issue but labels the CORRECT variance calculation 'critical': sqrt2-inverse
  scaling gives variance1/2 per real coordinate, total1, which is exactly proper
  CN1 and the claimed convention. Its assertion that this contradicts the same
  'variance1/2 per REAL coordinate' sentence is self-contradictory. No source change
  was made to accommodate that false alarm. Numeric missing-scale controls and
  exact realPair/entry pushforward proofs support the same normalization.
- Fin0 product Fintype is inferred by Lean; no positive-dimension assumption is
  needed for constant/empty products. ComplexSample is EuclideanSpace over real
  ((row,column),re/im), and complexMatrixEntries extracts entries without an
  extra scaling; complexSampleMatrix performs the sqrt2 division INSIDE.
- Map-integrability direction uses the exact pushforward equality; old SampleIdx
  real-coordinate polynomial variables are not reused as physical holomorphic
  variables. The new physicalEntryPolynomialMatrix has one variable per complex
  entry, and its evaluation identity is proved through map_det/map_mul.

[需人工审查] Finite coordinate/product transport, map-integrability, physical
variance and original model/paper interpretation. Full Lake/mathlib NOT_RUN.
Frozen manuscript/PDF/upload/code archives remain unchanged.
