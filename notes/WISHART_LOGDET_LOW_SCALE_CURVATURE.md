# Actual low-scale logdet curvature

For every finite shape m,n (including zero), any fixed deterministic complex M,
the existing variance-one CN source X=Z+M and natural-log full matrix statistic
C(r)=log det(I+r X^H X), set T=mn+SUM||Mij||^2. Then

    (r*T-E C(r))/r^2 -> (1/2) SUM_i E lambda_i^2, r->0right.

The right side is the finite ACTUAL probability integral, not empirical sample
data, a density hypothesis, or a claimed closed classical formula. All eigenvalues
including deterministic zeros of wide Gram matrices are retained. No rank,
smallest-eigenvalue positivity, inverse moment, joint spectral density or
channel-coding assumption is needed. All proof bodies Codex.

## Exact proof obligations

`LogDetLowScaleSecondOrder.lean` proves the scalar bound
0<=u-log(1+u)<=u^2 for u>=0 from mathlib log upper/lower bounds. The scalar
quotient limit x^2/2 uses ONE application of L'Hopital at0right: the derivative
quotient cancels to x^2/(2(1+r*x)) for r>0. Dominated convergence uses f^2 as an
integrable majorant, explicit AE measurability/nonnegativity and finite first
moment before rewriting integral_sub. The loose upper factor1 is sufficient
for domination; the sharp limit factor1/2 comes from the derivative calculation.
Finite sums and integrals are exchanged with each term explicitly integrable.

`ActualLogDetLowScaleCurvature.lean` derives source L4 from Fernique, gives
trace^2=||real_source+encodedM||^4/4, then lambda_i^2<=trace^2. It instantiates
the abstract finite-spectrum limit and the already proved actual matrix/spectral
identity and closed first moment. No second moment is assumed in this actual
theorem. Empty spectra are empty sums, not excluded implicitly.

## Reproducibility and review

Fixedseed2026101925,200000 samples per5 shapes, actual CN entry normalization,
noncentral trace/variance and scalar Gamma(n,1) second moment controls passed.
The proposed closed EtrW2 formula is checked numerically but NOT yet formalized.
No numerical fact enters the Lean proofs. P1 request timed out at90seconds;
its raw/receipt remain and do not count as a delivered route review. The final
route used locked local L'Hopital/DCT APIs, avoiding fresh Taylor infrastructure.
First two compile failures preserve function/module elaboration repairs; final
logdet-second-order-3 and actual-logdet-curvature-1 realexit0 with7 standard
three-axiom declarations. Main facade36 realexit0. Full build NOT_RUN.

Final-source real Qoder P4 is retained with these resolutions:

* Its claimed division-timing issue is false. `rw [integral_div] at ht` rewrites
  only the TARGET limiting integral of f^2/2 (there is no explicit r inside the
  abstract left-side lambda until the later eventually-equality step). Even a
  pointwise constant-divisor rewrite is an exact equality, not an illicit limit
  substitution. The combined fraction is preserved and cancellation uses r>0.
* Empty-spectrum concern: finiteSpectrumLogDet is literally a finite sum, so
  the generic theorem needs no Nonempty premise. Actual empty-column cases
  give0; positive-column/zero-row cases give zero eigenvalues and zero moments.
* Factor1/2 concern: the independent trace identity already accounts for the
  paired real source/sqrt2 encoding. No extra factor enters T; second scalar
  Taylor coefficient is exactly1/2.
* Reviewer calls RHS "empirical": this is inaccurate. It is an exact finite
  expectation over stdGaussian. Experiments are separate and not premises.
* Reviewer axiom metadata (funext) is inaccurate. Actual prints are propext,
  Classical.choice, Quot.sound; real compiler output is the authority.

Model review is not human review or independent compilation. [需人工审查]
Gaussian/variance and model correspondence, measure/limit steps, proof bodies
and paper mapping remain. Frozen manuscript/PDF/upload/code archives unchanged.

Next possible coefficient card: eliminate the remaining second-moment integral
using the existing exact Gaussian factorial functional and the polynomial
trace of the square of the actual noncentral Gram polynomial. The simplified
closed expression mn(m+n)+2(m+n)||M||F^2+tr((M^H M)^2) remains unproved.
