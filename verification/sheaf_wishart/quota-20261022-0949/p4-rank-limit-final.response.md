## P4 Adversarial Review: RegularizedSpectrumRankLimit.lean

**1. DCT Measurability Gap (Mathematical)**

In `integral_regularized_spectral_power_tendsto`, the domination proof fixes an arbitrary `r : ℝ` and establishes the bound `(r*f a/(1+r*f a))^k ≤ 1` only under the condition `0 ≤ r` (via `eventually_ge_atTop`). However, the first bullet supplies measurability for *all* `r : ℝ` unconditionally (`Eventually.of_forall (fun r => ...)`). For `r < 0` with `r*u < -1`, the denominator `1 + r*u` becomes negative or zero, breaking both the bound and potentially the measurability of the composition as stated. The DCT application requires the dominating function to uniformly dominate on the filter tail, but the measurability claim is over-specified. This is not fatal since `atTop` eventually restricts to `r ≥ 0`, but the unconditional `of_forall` wrapper is semantically imprecise and could mask a typeclass resolution failure if the measurable space structure depends on the sign constraint.

**2. Missing Finite Measure Proof Obligation (Mathematical)**

The theorem `actualCorrelated_regularized_spectral_power_rank_limit` applies `integral_regularized_spectral_power_tendsto` to `stdGaussian _`. The integral DCT theorem requires `[IsFiniteMeasure μ]`. While `stdGaussian` on a finite-dimensional complex sample space should be a probability measure (hence finite), this instance must be inferred. If the imported `ExpectedLogDetStrictConcavity` does not transitively provide `isProbabilityMeasure_stdGaussian` or `finiteMeasure_stdGaussian`, this is a hard gap. The source does not explicitly supply it; it relies entirely on typeclass inference from imports.

**3. Index Set Cardinality Mismatch (Mathematical)**

The sum in `actualCorrelated_regularized_spectral_power_rank_limit` ranges over `i : Fin (Fintype.card (Fin n))`, which has cardinality `n`. However, the rank limit is `min m (Matrix.fromRows B M).rank`. The eigenvalues being summed belong to `complexGram_posSemidef (complexSampleMatrix z * B + M)`, which is built from matrices with row types `Fin p` and `Fin m`. If the Gram matrix dimension is not exactly `n`, then summing indicator functions over `Fin n` either includes spurious zero-padding indices or truncates actual eigenvalues. The equality `he` bridges this via `gram_positive_modes_eq_rank`, but this step assumes the eigenvalue family `actualCorrelatedEigenvalue B M i` is indexed coherently with the Gram matrix dimension. A semantic mismatch between `n` and the actual spectral dimension would invalidate the counting argument.

**4. Derivative-Integral Commutation (API/Signature Question)**

The theorems `actualCorrelated_scaled_expected_logdet_deriv_rank_limit` and the curvature variant invoke `actualCorrelated_expected_logdet_hasDerivAt` and `actualCorrelated_expected_logdet_second_deriv` to replace `r * deriv (∫ ...)` with `∑ ∫ r * ...`. These are imported dependencies. The commutation of `deriv` and `∫` requires uniform domination of the derivative integrand, not merely pointwise differentiability. If the imported theorems only assert `HasDerivAt` without establishing the domination hypothesis that justifies passing the derivative through the Gaussian integral, this is a logical gap in the dependency chain, not merely an API question.

**5. Almost-Everywhere Rank Constancy Interpretation (Mathematical)**

The proof of `he` uses `actualCorrelatedRank_eq_generic_ae B M` to replace the pointwise eigenvalue count with the deterministic value `min m (fromRows B M).rank` inside the integral. This is valid only if the generic rank equals the deterministic matrix rank of `fromRows B M` for *fixed* `B, M`. If `actualCorrelatedRank` refers to the rank of the random matrix `z*B + M` and the AE statement asserts this equals `rank(fromRows B M)` almost surely, then the substitution is correct. But if the AE generic rank depends on properties of `B` and `M` beyond their stacked rank (e.g., requiring full-rank conditions not stated in the theorem signature), this is an unstated assumption gap.
