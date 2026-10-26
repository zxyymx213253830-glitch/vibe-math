# Next: full noncentral radial moments and candidate G2 normalization

Actual matrix PSD Laplace, uniqueness, sorted-orbit and rank-L positive
parameter mapping are closed. Candidate G2 still needs normalization and
actual-law identification. Scalar trace Laplace does NOT determine a joint
spectrum law, and the eigenvalue candidate alone does not specify the angular
matrix law for anisotropic noncentrality. Do not use PSD uniqueness to skip
these obligations.

Potential next bounded target, not a current theorem: for q,k natural,
a real, lambda=a^2/2, the already normalized even radial kernel has

 integral_(r>0) (r^2/2)^k K_q(a,r) dr
   = k! * sum_(j=0..k) choose(k+q,k-j)*lambda^j/j!.

This is a polynomial full-moment identity, including a=0 and k=0. It is not a
Wishart G2 law. Before source, make new fixed-seed quadrature/Gamma/noncentral
chi-square moment controls, negative factor2 and shifted-shape controls.
No new controls or source for this target have yet been written.

Reuse NoncentralEvenDimensionalPoissonMixture.noncentralChiEvenRadialKernel_eq_poissonMixture,
EvenRadialProbability normalization and EvenRadialWeightedIntegral full near0
MGF/integrability. Do not redo the kernel mixture, mass1, actual one-column
law or weighted MGF. GammaIntegerMoments/GaussianOddMoments may supply the
central power integral. The finite sum can follow from Vandermonde's identity
for choose(q+j+k,k), factorial cancellation and the exponential series; the
nonnegative kernel permits Tonelli before showing real integrability. Inspect
exact pinned APIs and avoid unstated differentiation under the integral.

If full moments are established, generic Andreief normalization can reduce the
candidate determinant integral to a finite polynomial moment determinant.
General partial-rank confluent Vandermonde constants and actual spectral-law
identification remain separate. Original repeated-parameter formulas may need
limits; do not assert them from rank-L extraction.

All Lean serial shared compute.lock, no budgets/dependency upgrades. No new
external disclosure is authorized for unseen modules: ask only after a concrete
locked source and review prompt exist. Current consent covers only the named
completed modules. [需人工审查] Tonelli/integrability/model/paper conventions.
