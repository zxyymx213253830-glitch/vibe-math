# General central Bartlett route: proved blocks and next density obligation

For m>=1, n>=0 and the actual CN(0,1) matrix [u,V], define off u=0
`r=||u||^2`, `z_j=<u,V_j>/||u||`, `B=V^H V-z^H z`.
Original target, now CLOSED (2026-10-18): joint `(r,z,B)` law equals Gamma(m,rate1) times
CN(0,I_n) times actual complexWishart(rows=m-1,columns=n).
Trace or determinant marginals alone are not this matrix-valued law.

Seed20261017, three shapes with 200000 samples each passed Gamma r/z/B-trace,
residual logdet moment, joint and direction/radius-bin controls. Numerical
evidence only, recorded in verification/central_bartlett_step/control.json.
Qoder's real P1 request/response is stored beside it, without invented proof
or source claims.

## Route decision after checking exact assets

Use **fixed-u complex unitary frame, explicit joint invariant map, then
skew_product**. Qoder preferred a covariance route and was unsure whether
skew_product needs a measurable frame. The actual locked theorem resolves it:

`MeasurePreserving.skew_product` in Mathlib/MeasureTheory/Measure/Prod.lean
requires `Measurable (uncurry g)` and `a.e. u, map (g u) mu = nu` for a constant
target measure nu. It does not require measurability of auxiliary objects
used only inside a proof of the fixed-u law. Here g is defined directly by
inner products/division and the residual Gram, not by a selected frame.

Thus a complex frame may be chosen separately **inside the proof for fixed
nonzero u**, used with Gaussian invariance to identify that fiber law. Its
choice is never part of g, so no joint measurable frame theorem is assumed.
The existing random-subspace energy proof already uses this exact pattern.
[需人工审查] Joint measurability/null exceptions and the eventual matrix-valued
law need semantic checking; this route note is not that proof.

Do not accept the following suggestions without correction:

- `(u,V)` being Gaussian does not make the nonlinear random projection
  `P_u V` jointly Gaussian with u. Fixed-u covariance arguments are legitimate;
  a global jointly-Gaussian shortcut would be false.
- A basis-free description of the residual covariance alone is not the
  actual lower-dimensional Wishart pushforward. A fixed isometric
  identification and the law of ALL remaining columns must be supplied.
- Claims about topological phase obstruction or a guessed number of lines
  are not verified library facts and do not drive the selection.

## Original cards and current status (2026-10-18)

1. CLOSED: Complex unit-vector frame existence, no measurable-selection claim.
2. CLOSED: A fixed complex unitary acting on every remaining column preserves its
   actual Gaussian matrix law; use real isometry and fixed coordinate curry.
3. CLOSED: For fixed nonzero u, identify the entire z and residual B with disjoint
   first-row/lower-row coordinates after rotation. They have product law.
4. CLOSED: Define the joint invariant g directly, patch u=0 measurably, exclude it by
   actual one-column Gamma law, and use skew_product.
5. PARTIAL: full-dimensional real Hermitian block splitting is volume preserving;
   positive-pivot fiber scaling/translation and Tonelli give the general r^n
   weighted volume map in canonical coordinates. Actual CN(n) density and
   central/noncentral t>=s absolute continuity are now proved. The closed
   determinant/trace density and its normalization recurrence remain open.

The parallel determinant objective is CLOSED: actual t-by-s central determinant
has the product law of independent Gamma(t-s+1,...,t;rate1), proved from the
entire block law, not only residual energies. Evidence is bound in
verification/bartlett_gram_reconstruction/audit.json. The volume and actual
absolute-continuity evidence is in verification/bartlett_fiber_volume/audit.json.
Both are actual-model results; neither is the missing explicit general
matrix density or spectral G2. Prior paper/PDF/submission artifacts are frozen
and do not yet include this new research. [需人工审查] remains for the stated
measure, variance and model correspondence.
