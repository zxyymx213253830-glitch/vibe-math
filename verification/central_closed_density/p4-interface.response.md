# P4 Skeptical Semantic Review

## Rates and scaling (CentralWishartScaledMinimum)

The claimed rate is `n/v` for complex variance `v`. The final theorem `actualCentralSquare_covariance_minimum_law` states the law is `expMeasure ((n : ℝ) / v)` after scaling by `√v`. This is consistent: if `z` has variance 1 per real component, then `√v • z` has variance `v`, and the minimum's tail decays as `exp(-n·x/v)`, giving rate `n/v`. No error here.

However, the `[需人工审查]` flag on "Gaussian amplitude versus complex covariance" is warranted semantically. The proof treats `ComplexSample` with `stdGaussian` as having unit complex variance, but the formalization never explicitly defines what "complex variance 1" means in terms of real/imaginary component variances. If `stdGaussian` assigns variance 1 to each of the 2n² real components, then the complex entries have variance 2, not 1. The rate `n/v` would shift by a factor of 2 depending on convention. **This is a concrete semantic gap**: the mapping from `stdGaussian (ComplexSample ...)` to the physical claim "variance v" requires an explicit convention linking real-component variance to complex variance. The code assumes this implicitly via `complexSampleGram_real_smul` producing `a² • Gram`, but whether `a² = v` or `a² = 2v` depends on unstated conventions.

## Matrix-vs-coordinate measures (CentralWishartMatrixDensity)

The definition `hermitianAmbientCoordinateMeasure n := (hermitianRealCoordinateMeasure n).map hermitianOfRealCoordinates` is correct as a pushforward of n²-dimensional real Lebesgue measure onto the Hermitian locus inside ℂ^{n×n}. The comment explicitly disclaims ambient 2n²-dimensional volume—good.

**Concrete issue**: `centralWishartMatrixDensity` uses `A.det.re ^ d * exp(-A.trace.re)`. For Hermitian `A`, determinant and trace are already real, so `.re` is redundant but harmless. However, the density is defined on all ℂ^{n×n} (returning 0 outside PD), while the reference measure is supported only on Hermitian matrices. This is semantically fine—the Radon-Nikodym derivative is only meaningful on the support—but the statement `complexWishart_eq_matrixDensity` equates a measure on ℂ^{n×n} to `withDensity` against a measure also on ℂ^{n×n} but concentrated on Hermitians. **No mathematical error**, but readers might misinterpret this as saying Wishart has a density w.r.t. full ambient Lebesgue measure, which it does not.

## Inverse mass and conditional law (CentralWishartConeMemoryless)

The unnormalized residual law multiplies by `exp(-nx)`. The conditional version applies `(ENNReal.ofReal (exp(-nx)))⁻¹ •`. Since `exp(-nx) > 0` and finite for `x ≥ 0`, the inverse exists in ENNReal and the cancellation `inv_mul_cancel` is valid. **No problem at n > 0.**

**At n = 0**: The theorems carry hypothesis `hx : 0 ≤ x` but no `hn : 0 < n`. At `n = 0`, matrices are 0×0 (trivial), `exp(-0·x) = 1`, and the statements reduce to trivial identities on the one-point space. The memoryless theorems remain technically true but vacuous. The prior note "at n=0 only trivial matrix/cone identities, not minimum law" is respected—no minimum theorem here attempts n=0. **No error.**

## Theorem strength and indicator handling

`centralWishartSquareDensity_shift_indicator` correctly handles both membership cases, using that the density vanishes outside the positive cone. The equivalence `q + x•1 ∈ shiftedCone ↔ q ∈ positiveCone` relies on `hermitianOfRealCoordinates_shift` and exact cancellation. **Sound.**

The composition `(fun q => q - x•1) ∘ (fun q => q + x•1) = id` is proved pointwise—correct, and avoids any need for injectivity arguments on maps between measure spaces.

## Dimension-zero edge case in normalization (CentralWishartNormalization)

At `n = 0`, `Fin 0` is empty, so `∏ j : Fin 0, ... = 1` and `0.choose 2 = 0`, giving `π⁰ / 1 = 1`. The base case `simp [centralWishartDensityConstant]` must resolve the constant to 1 at `n=0`. **Assuming the upstream definition gives `centralWishartDensityConstant d 0 = 1`**, this is fine; otherwise the `zero` arm fails. Not checkable here without the definition, but standard.

## Fubini/volume/model mapping flags

All four files carry `[需人工审查]` or similar flags. The specific unresolved item is whether `hermitianRealCoordinateMeasure` correctly represents the intended physical model's reference volume. The formalization consistently uses nested Π-Lebesgue (coordinate) measure, not Frobenius-norm-induced volume. These differ by a constant factor `2^{n(n-1)/4}` or similar depending on convention. **This is not a bug within the formalization**—it is self-consistent—but it means the numerical value of `K(d,n)` cannot be compared to physics/statistics literature without an explicit Jacobian translation. The review prompt acknowledges this was flagged previously.

## Summary of concrete issues

1. **Variance convention gap**: The mapping from `stdGaussian (ComplexSample)` to "complex variance v" lacks an explicit definition. Rate `n/v` is internally consistent but may differ from standard statistical convention by factor 2.
2. **Ambient measure confusion risk**: `hermitianAmbientCoordinateMeasure` lives on ℂ^{n×n} but is singular; the density theorem is correct but could mislead readers about absolute continuity w.r.t. full Lebesgue measure.
3. **Upstream dependency**: Normalization at `n=0` requires `centralWishartDensityConstant d 0 = 1` from the imported file.

No logical errors, no missing side conditions, no strength mismatches detected within the four files as given.
