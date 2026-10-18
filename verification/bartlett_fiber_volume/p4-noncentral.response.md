# Review: Noncentral Wishart Absolute Continuity

## Density Orientation in Shift Theorem

In `stdGaussian_shift_eq_withDensity`, the density is `euclideanStdGaussianDensity (z - μ)`. This is correct: if Y = X + μ where X ~ stdGaussian, then Y has density f(y - μ) with respect to Lebesgue measure. The subtraction orientation matches the pushforward direction.

## Actual-vs-Candidate Density

The proof correctly uses the **actual** shifted density (via `stdGaussian_shift_eq_withDensity`) rather than a candidate Radon-Nikodym derivative. The domination argument chains through the true density being strictly positive everywhere, which is sound. No explicit noncentral Wishart density is claimed—only domination.

## Reference Measure Chain

The three-step chain in `stdGaussian_shift_absolutelyContinuous` is:
1. Shifted Gaussian ≪ volume (via explicit density)
2. Volume ≪ standard Gaussian (via strictly positive central density)
3. Transitivity

Step 2 requires that `euclideanStdGaussianDensity x > 0` for all x, which holds since the exponential is always positive and the normalization constant `(√(2π))⁻¹ ^ card ι` is positive. The use of `withDensity_absolutelyContinuous'` with pointwise positivity is valid.

## Mean Encoding and Variance

The `complexSampleMean M` encoding must satisfy: if Z has variance-1 real coordinates, then Z + complexSampleMean(M) encodes mean M without changing variance. The √2 convention for complex-to-real embedding ensures each complex entry with unit real/imaginary variance maps correctly. If this identity were wrong, the pushforward would not land on `complexNoncentralWishart M`.

## Null-Set Transport

Pushforward preserves absolute continuity: if μ ≪ ν then μ.map f ≪ ν.map f for measurable f. This is applied twice (first for Gram map, then for coordinate map). The concern is whether null sets of the central Wishart (which lives on singular matrices when n > m) could fail to capture noncentral null sets—but domination means exactly that central-null implies noncentral-null, regardless of singularity.

## Wide Matrices and Dimensionality

For n > m, both central and noncentral Gram measures are supported on rank-≤m matrices, hence singular w.r.t. full n²-dimensional Lebesgue measure. Domination still holds because they share the same lower-dimensional support structure. The final theorem restricts to s ≤ t, where `hermitianRealCoordinateMeasure s` is the appropriate full-dimensional reference.

## Zero Dimensions

When ι is empty (Fintype.card = 0), the space is a point, stdGaussian is δ₀, shift by a=0 gives δ₀, and domination holds trivially. The density becomes `(√(2π))⁰ · exp(0) = 1`, which is positive.

**Verdict:** No concrete mathematical errors identified. The null-set chain, density orientation, and pushforward logic are consistent. Human review should verify the `complexSampleMean` encoding identity and the measurability of `complexSampleGram` under the specific library conventions.
