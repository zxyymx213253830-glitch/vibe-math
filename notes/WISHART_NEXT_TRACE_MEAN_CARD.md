# Next bounded card: explicit actual Gaussian expected trace

Current420/facade38: ALL finite shapes/fixedcomplexM actual Etrace=mn+F and Etrace(Gram^2)=mn(m+n)+2(m+n)F+trace((M^HM)^2).re, F=SUM||Mij||^2. Full-logdet lowrho first/second coefficients now CLOSED, no rank/inverse-moment/density premise. Earlier unproved-mean/second-moment statements below are historical and superseded. Finalsource realQoderP4 delivered/resolved; humanreview/frozenpublication/fullbuild boundaries unchanged. See WISHART_GAUSSIAN_TRACE_MEAN.md and WISHART_NONCENTRAL_SECOND_MOMENT_CLOSED.md.

Current verified checkpoint:387 bound items including the generic
GaussianSquaredNormShift helper, final leaf/main-entry33 checks and scoped
real P4 response. Its review axiom list is incorrect: actual printed axioms
are propext, Classical.choice, Quot.sound, not funext. The actual finite-scale logdet bound and low-scale slope use
T=actualExpectedGramPower M. They do NOT yet identify it with the classical
m*N+SUM_ij ||M_ij||^2. Do not silently substitute that numerical control value.

Selected route A: even-dimensional Gaussian Gamma energy plus centered
squared-norm shift. Rejected alternatives for this small obligation: rebuilding
entrywise covariance/independence; expanding the full Gaussian polynomial
functional; reproving radial integration. The needed exact assets were read:

* GaussianOrthogonalProjectionLaw.stdGaussian_half_norm_sq_law k hk hdim:
  map(stdGaussian E,z->||z||^2/2)=gammaMeasure(k,1), k>0,
  finrank_REAL(E)=2*k. For ComplexSample(m,n) the real dimension is2*m*n.
* GammaIntegerMoments.lintegral_gammaMeasure_nat_power k p:
  nonnegative moment of Gamma(k+1,1) is (k+p)!/k!. At p1 this gives k+1,
  using Nat.factorial_succ and nonzero factorial casts.
* GaussianGramLogMoments.integrable_actualNoncentralGram_trace and mathlib
  IsGaussian.memLp_two_id/integrable_norm_pow' give L1 before interpreting
  real expectations. ofReal_integral_eq_lintegral_ofReal converts only under
  these integrability/nonnegativity hypotheses.
* GaussianSquaredNormShift.integral_stdGaussian_norm_sq_add is the new
  checked helper: E||z+v||^2=E||z||^2+||v||^2. It uses the existing exact
  integral_strongDual_stdGaussian=0, NOT an assumed complex mean-zero model.
* complexSampleGram_trace_half_norm and complexSampleMatrix_add_mean give
  tr(Gram(complexSampleMatrix z+M))=||z+complexSampleMean M||^2/2.
* complexSampleMatrix_complexSampleMean M=M and complexGram_trace_re give
  ||complexSampleMean M||^2/2=SUM_ij ||M_ij||^2.

Small remaining obligations, with exact targets:

1. For k>0, finrank_REAL E=2*k, derive the REAL integral E||z||^2/2=k from
   the actual pushforward Gamma law and existing nonnegative first moment.
   Match Gamma(k,1) with a successor representation; do not lose a factorial
   or divide by a possibly zero natural cast. Handle k0 separately.
2. Establish the displayed norm-of-encoded-mean identity by existing matrix
   encoding/trace assets, not a new coordinate expansion.
3. Combine with the checked shift helper and integral linearity to prove
   actualExpectedGramPower M=(m*n:REAL)+SUM_ij ||M_ij||^2, all dimensions.
   If m*n=0, use the zero-dimensional source/empty sums explicitly.
4. Only after the actual identity passes, substitute it into the existing
   full-logdet finite-rho upper bound and low-rho slope. These last two are
   interfaces, not separate new probability breakthroughs.

Numerical preflight is already independently present: fixedseed2026101921
and2026101924 actual CN traces with noncentral known first moment and variance,
plus earlier Gamma/trace controls. Reuse their exact hashes and failure records;
do not redraw samples just to consume quota. New symbolic/number controls, if
needed for an altered conjecture, must precede its proof.

All future Lean through the same collaborative_check.py/session/library gate;
the current technical lease is a process safeguard, not permission to work
after actual ordinary quota becomes unavailable. Final-source P4 from the
different model family must preserve real responses, not approve pseudo-tools.
[需人工审查] Measure/variance/real-vs-complex and physical model mapping remain.
Frozen manuscript/PDF/upload archives remain old and unchanged.
