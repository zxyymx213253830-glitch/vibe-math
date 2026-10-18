## Remaining Concrete Issues

**1. Variance naming inconsistency (minor, not mathematical)**

`standardComplexColumnLaw` scales by `(Real.sqrt 2)⁻¹`, which correctly produces variance 1 per complex entry (real/imaginary parts each have variance 1/2). However, `GaussianComplexColumnDensity.lean` references `stdGaussian_halfVariance_shift_eq_withDensity`. If that theorem's "half-variance" refers to the real component variance of 1/2, the naming is consistent—but verify this identifier actually exists and matches. The density `π⁻ⁿ exp(-‖z‖²)` is correct for CN(0,1). **No factor-two error in the math itself.**

**2. Volume convention must be documented, not corrected**

The choice to use canonical coordinate volume (where off-diagonal pairs contribute volume factor 2 each, totaling `2^(n(n-1)/2)`) rather than Frobenius-induced volume is **mathematically valid** but must be explicitly stated in docstrings. This is a convention choice, not an error. If downstream results (e.g., Bartlett decomposition Jacobians) assume Frobenius volume, they will silently mismatch. **Action: add a documentation note at the top of the relevant file stating which volume form is used.**

**3. Rate n/v claim: no error given stated premises**

Given:
- `complexSampleMatrix` entries have variance 1 (confirmed by construction)
- Scaling source by `√v` yields variance `v` (correct: `(√v)² · 1 = v`)
- Leading diagonal Bartlett energy has shape = row count `n`, rate 1 for unit variance

Then for variance `v`, the minimum eigenvalue/energy is indeed `Exp(rate = n/v)`. **No concrete error here**, provided the Bartlett decomposition correctly tracks the variance scaling through the change-of-measure. Verify that the scaling by `√v` is applied to the *sample matrix before* forming `W = X*X`, not after.

**4. `[需人工审查]` tag in GaussianComplexColumnDensity.lean**

The tag requesting human review for "Orthonormal/Haar normalization, real vs complex variance convention" should be resolved or removed now that you've clarified the convention. Leaving unresolved review tags on proven theorems creates false alarm.

**Summary:** No actual factor-two or rate error remains given the explicit constructions shown. The only actionable item is **documentation**: state the volume convention explicitly and remove stale review tags.
