# Actual Gaussian Gram log-det: finite moments, offset and prelog

2026-10-19. Proofs: Codex. Bounded Qoder P1 timed out, not a route approval.
Final-source P4 requests/real responses are preserved separately from proofs.
[需人工审查] Measure, Gaussian variance, spectral and channel interpretation.

Let X=Z+M, where Z is an m by N matrix of independent CN(0,1) entries,
E|Z_ij|^2=1, and M is any fixed deterministic complex matrix. Assume m>=N>0.
Define, in natural-log units,

    C(rho,X)=log(Re det(I_N+rho*X^H X)), rho>=0.

The determinant is real positive here. A checked deterministic spectral
identity identifies C with SUM_i log(1+rho*lambda_i(X^H X)); thus the result
concerns the complete matrix statistic, not just the weakest eigenmode.

The actual-law statements now checked are:

* C(rho,X) is integrable for every fixed rho>=0, even without m>=N.
* For m>=N>0, log(Re det(X^H X)) is absolutely integrable.
* E C(rho,X)-N log(rho) -> E log(Re det(X^H X)) as rho->infinity.
* Consequently E C(rho,X)/log(rho) -> N.

No joint spectral density or explicit noncentral CDF is assumed. M is FIXED;
no uniformity for M depending on rho or degenerating covariance is claimed.
This is a classical probability/asymptotic statistic formalized in Lean, not
a new communication coding theorem or a derivation of Gaussian-channel mutual
information. If a channel convention uses rho/N, the prelog is unchanged but
the constant offset changes by -N log N; that physical mapping is not silently
included. Logs in bits require the corresponding log2 conversion.

## Proof chain and square-case safeguard

1. Pinned mathlib Gaussian Fernique/Lp results show the squared norm of the
   shifted standard-real source is integrable. The existing source encoding
   gives tr(X^H X)=||z+complexSampleMean(M)||^2/2 exactly.
2. Reuse the previously proved full complex Hermitian Weyl continuity result
   for all ordered eigenvalue coordinates. Each eigenvalue is measurable and
   lies between the minimum and the nonnegative trace, so is integrable.
3. The prior actual inverse-minimum theorem supplies an inverse HALF moment:
   1/2<m-N+1 for every m>=N. This does not require a finite FIRST inverse
   moment, which is false in the square case. The eigenvalue inverse half
   moments are dominated by the minimum's inverse half moment.
4. A generic lemma proves log f integrable from integrable positive-AE f and
   any positive inverse p moment. Its pointwise envelope is
   |log f| <= f+(f^-1)^p/p. Values on the rank-deficient nullset are handled AE;
   Lean's real log0/inverse0 conventions are not used as an excuse for
   integrability, and no divergent real Bochner integral is treated as infinity.
5. For rho>=1 and f>0, log(f+1/rho) is bounded between log f and log(1+f).
   The envelope |log f|+f is integrable. Filter-form dominated convergence gives
   E log(f+1/rho)->E log f. Actual individual integrability justifies all finite
   sums and integral subtraction; the probability-mass1 factor is explicit.
6. The exact identity log(1+rho*f)-log(rho)=log(f+1/rho), rho>0, gives the
   expected full-spectrum offset. Dividing the bounded-convergent offset by
   log rho->infinity gives the prelog N.
7. Unitary diagonalization, determinant multiplicativity and unitary inverse
   cancellation identify the finite spectral sum with the actual matrix
   log-det; all log_prod factors are proved positive before use. The unshifted
   logdet=SUM_i log(lambda_i) identity is used only on the full-rank AE set.

## Exact assets, controls and validation

Reused: actualNoncentralRectangular_inverseMinimum_realMoment_integrable_iff,
actualNoncentral_minimum_pos_ae, complexSampleGram_trace_half_norm,
complexSampleMatrix_add_mean, orderedHermitianEigenvalueCoordinatesContinuous,
mathlib IsGaussian.memLp_two_id/integrable_norm_pow', Real.log_le_rpow_div,
filter dominated convergence, and Matrix.IsHermitian.spectral_theorem.
Rejected: relying on finite E[1/lambda_min] for m=N; inferring convergence of
expectations from AE convergence alone; treating worst-mode outage as full
matrix capacity; assuming Gaussian independence of ordered eigenvalues.

Fixedseed2026101921,200000 actual CN samples per shape (1,1),(2,2),(4,2),(5,3)
check direct slogdet vs eigensum, known scalar exp(1/rho)*E1(1/rho), noncentral
trace expectation/variance and an incorrect N/2-prelog negative control.
The first script erroneously demanded finite-rho prelog error<0.2, omitting
the Elogdet/logrho bias; it failed. That failure and original source hash are
retained. The corrected control checks the exact finite offset and its
decreasing nonnegative remainder; PASS is numerical support, not proof.
The P1 prompt was sent before this incidental tolerance failure was corrected;
its output timed out, so it supplied no review of either version.

Six new modules have25 printed declarations: LogMomentIntegrability3,
GaussianGramLogMoments6, FiniteSpectrumLogDetGrowth3,
NoncentralGramLogDetGrowth3, HermitianSpectralLogDet4, ActualGramLogDet6.
The generic finite sum/log lemmas are infrastructure, not25 new probability
discoveries. Final leaf logs: log-moment-2, gram-log-moments-4, finite-logdet-2,
noncentral-logdet-2, hermitian-logdet-3, actual-logdet-1. Each real exit0; all
printed axioms are the standard three. Main entry facade-27 real exit0.
Full Lake/mathlib build NOT_RUN. Frozen manuscript/PDF/upload archives unchanged.

The new generic log-moment envelope and log-shift integral interface wrap
existing mathlib calculus/Lp/DCT rather than replacing it. Their exact upstream
novelty is not claimed. The application combines these with previously checked
actual noncentral inverse-moment and spectrum laws.

## Generic P4 response and resolution

The real generic P4 response delivered two objections, not a blanket approval.
Its proposed domination defect is a misreading: source hu is exactly
log(f+1/rho)<=f+1/rho-1, NOT log f+1/rho. Together with 1/rho<=1 this gives
log(f+1/rho)<=f<=|log f|+f directly. Source hl gives log f<=log(f+1/rho),
and -|log f|<=log f with f>0 gives the lower absolute bound. These are the
precise local hypotheses fed to the successful checked linear arithmetic;
no case split, concavity or 1/rho<=f is required. No source change is warranted.
The second objection says the abstract spectral theorem has not itself proved
actual eigenvalue integrability. That is a separate application obligation,
discharged in the simultaneously reviewed GaussianGramLogMoments and
NoncentralGramLogDetGrowth modules, not assumed as a target density premise.
The split prompt explicitly identified these as separate review groups.
The raw objections are retained in full, not edited into an approval.

The actual-chain P4 also delivered. Its two conditional import concerns are
resolved against exact pinned statements: NoncentralInverseMinimumRealMoments
actually states integrability under stdGaussian(ComplexSample(m,n)), arbitrary
fixed M, m>=n>0, not an abstract spectrum law or a target-density hypothesis.
NoncentralInverseMinimumTail.actualNoncentral_minimum_pos_ae has the same
actual source measure and arbitrary M with only n>0,n<=m; it inherits actual
Gaussian full-rank AE, not a rank assumption on M. The eigenvalue definition
is explicitly the sorted spectrum of complexGram(complexSampleMatrix z+M).
These imported source and olean hashes are already bound in this bundle.
The response finds no remaining internal logical issue given those imports.
Its phrase L2-integrability of the norm squared is imprecise: the code uses
source in L2 to obtain L1-integrability of its squared norm; no L4 premise is
needed. All original wording remains in raw responses. Neither response is
human approval or independent compilation; human review remains required.
