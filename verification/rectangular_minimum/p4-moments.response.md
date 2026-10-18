# P4 Semantic Review

## GammaIntegerMoments.lean

**Factorial range and shape indexing.** Theorem `gammaPDF_nat_power_shift` shifts shape from `k+1` to `k+p+1`. This is correct: multiplying a Gamma(k+1,1) density by r^p yields an unnormalized Gamma(k+p+1,1) density, with proportionality constant Γ(k+p+1)/Γ(k+1) = (k+p)!/k!. No off-by-one.

**Measure-theoretic transport.** `gammaMeasure_nat_power_bias` uses `withDensity_congr_ae` restricted to `Ioi 0`. Valid because `gammaMeasure_nat_succ_absolutelyContinuous_positive` gives a.e. positivity. However, the `ENNReal.ofReal_ne_top` side condition on `withDensity_smul'` requires that the scalar `(k+p)!/k!` viewed as ENNReal is not ⊤. This holds for all concrete naturals but relies on the coercion path `ℕ → ℝ → ENNReal` never hitting infinity. Lean's `ENNReal.ofReal` maps negative reals to 0 and positive finite reals to finite ENNReals, so this is fine—but the proof obligation is discharged silently by `norm_num` or `positivity` without explicit mention. Low risk.

**Absolute value handling.** `lintegral_gammaMeasure_nat_abs_power` replaces `|r|^p` with `r^p` using a.e. positivity of the Gamma support. Correct. The `ae_le` application with `ae_restrict_mem measurableSet_Ioi` properly restricts to the open ray. No issue.

**Zero dimensions.** When `k = 0`, shape = 1, which is Exp(1). Factorials are `Nat.factorial p / Nat.factorial 0 = p!`. Correct. When `p = 0`, ratio is 1, integral is total mass = 1. Consistent.

## GaussianSubmatrixLaw.lean

**Injective coordinate projection.** `pi_gaussianReal_map_injective` decomposes via `measurePreserving_piEquivPiSubtypeProd`, projects onto `range e`, then transports back via `eR : κ ≃ range e`. This is the standard argument. One subtlety: `measurePreserving_fst` discards the complement coordinates `{i // i ∉ range e}`. This is valid because the product measure factors and we integrate out the unused coordinates—marginalization of independent Gaussians yields independent Gaussians. No variance rescaling needed since we select, not average.

**Real-to-Euclidean transport.** `stdGaussian_map_injective_coordinates` chains `WithLp.toLp 2` coercions. The composition identity `hf` is definitionally true (`rfl`). The double `map_map` reversal correctly peels off the EuclideanSpace wrapper, applies the index-level result, then re-wraps. Sound.

**Complex source entries.** The review prompt states entries are `(z0 + i*z1)/√2` with `z0, z1 ~ N(0,1)` real. Critically, `ComplexSample` is indexed as `((Fin m × Fin n) × Fin 2)`, where the `Fin 2` separates real/imaginary parts. The injection `he : Function.Injective e` on column indices lifts to injectivity on the triple product because `e` acts only on the `Fin n` component while `Fin m` and `Fin 2` pass through unchanged. The proof in `stdGaussian_sampleColumnSelection_law` handles this correctly: `hj : e j = e j'` combined with `he` forces `j = j'`. **No variance mismatch**: selecting columns does not alter the per-entry distribution; each selected entry remains `(z0 + i*z1)/√2` with the same law.

**Gram principal submatrix.** `complexGram_columnSelection` is a direct matrix computation: `(X.submatrix id e)ᴴ * (X.submatrix id e) = (Xᴴ * X).submatrix e e`. Verified by extensionality. The Wishart pushforward `complexWishart_principalSubmatrix_law` then follows functorially. **This confirms P1 correction**: row count `m` is unchanged; only columns are selected. Surplus rows `m - k` do not appear—the Gram matrix is `k × k` regardless of `m ≥ k`.

**Zero dimensions.** If `k = 0`, `e : Fin 0 → Fin n` is vacuously injective. `ComplexSample (n := 0)` is a zero-dimensional space. `stdGaussian` on empty type is unit mass at the unique point. All theorems hold trivially. If `n = 0` but `k > 0`, no such `e` exists (cannot inject `Fin k` into `Fin 0`), so theorems are vacuously applicable. Consistent.

## CentralWishartDeterminantMoments.lean

**Product law probability instance.** `isProbabilityMeasure_centralBartlettGammaProductLaw` transfers the instance through `complexWishart_det_eq_gammaProduct`. This requires the determinant map to be measurable and the pushforward of a probability measure to remain a probability measure. Standard.

**Tonelli/product splitting.** `lintegral_prod_mul` splits the integral over `ℝ × ℂ` into separate integrals. Requires nonnegativity of both factors, which holds since `ENNReal.ofReal (|r|^p) ≥ 0` and similarly for `‖z‖^p`. The induction step correctly casts `Fin (n+1)` via `castSucc`/`last`.

**Factorial ratio telescoping.** `factorial_ratio_product` collapses `∏ (d+j+1)!/(d+j)!` to `(d+n)!/d!`. Pure algebra, verified by induction. Base case `n=0` gives empty product = 1 = `d!/d!`. Correct.

**Mean specialization.** Setting `p=1` in the moment formula and applying the telescoping product yields `E[|det W|] = (d+n)!/d!`. The `ENNReal.ofReal_prod_of_nonneg` step pulls the product inside `ofReal`, requiring each factor nonnegative—guaranteed by factorial ratios being positive.

**Reindexing by total dimension.** `complexWishart_determinant_norm_mean_of_le` substitutes `t = d+s`, so `d = t-s`. The constraint `s ≤ t` ensures `t-s` is a valid natural. This is purely cosmetic but correctly stated.

**Variance consistency check.** The actual determinant law uses `Gamma(d+j+1, rate=1)` for `j = 0..n-1`. These arise from squared norms of complex Gaussians with variance 1 per real/imaginary part (total variance 2 per complex entry, but the `1/√2` normalization in `ComplexSample` makes each entry standard complex normal with E[|z|²] = 1). The Bartlett decomposition then produces chi-squared/Gamma variables with rate 1. **No hidden factor of 2 error.**

## Summary of Concrete Issues Found

1. **Low severity:** `gammaMeasure_nat_power_bias` discharges `ENNReal.ofReal_ne_top` implicitly. While mathematically sound, an explicit `simp [ENNReal.ofReal_ne_top]` or comment would improve auditability.

2. **No blocking issues detected.** Index orientations, zero-dimensional edge cases, measure transports, factorial ranges, and real-vs-complex variance are handled correctly across all three files.
