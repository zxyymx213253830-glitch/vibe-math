# P4 Semantic Review: Central Wishart Minimum Exponential Law

## Dimensional Consistency

**No problem found.** The rectangular parameterization `m = d + n` with `d : ℕ` as surplus rows correctly yields the square case at `d = 0`. The Bartlett pivot uses `gammaPDF ((d + n + 1 : ℕ) : ℝ) 1`, matching the leading diagonal entry's chi-squared degrees of freedom for a `(d+n+1)`-row complex Gaussian column. The residual Gram has dimension `n × n`, consistent with the induction hypothesis on `centralWishartCoordinateDensity d n`.

## Strict vs. Non-Strict Events

**No problem found.** The cone `{q | (hermitianOfRealCoordinates q - x • 1).PosDef}` encodes the **strict** inequality `x < λ_min` via positive-definiteness, not merely positive-semidefiniteness. The threshold lemma `centralSquareSampleMinimum_threshold` correctly uses `x < centralSquareSampleMinimum`, and the CDF complement `{z | x < ...}ᶜ = {z | ... ≤ x}` is exact by `not_lt` on reals. No measure-zero boundary ambiguity arises because the minimum eigenvalue distribution is absolutely continuous.

## Reference Volume and Coordinates

**No problem found.** `hermitianRealCoordinateMeasure n` is the canonical `n²`-dimensional real Lebesgue measure on Hermitian matrices (diagonal entries real, off-diagonal entries as real-imaginary pairs), not the Frobenius-induced volume that would carry an extra `2^{n(n-1)/2}` factor. The density `centralWishartCoordinateDensity` is defined against this reference, and the normalization `lintegral_centralWishartCoordinateDensity = 1` derives from the actual probability law rather than being postulated.

## Exponential Rate Verification

**No problem found.** For square `n × n` (`d = 0`):
- The determinant factor becomes `(det(...))^0 = 1`, eliminating all polynomial terms.
- The trace shift yields exactly `exp(-n * x)` since `trace(x • I_n) = n * x`.
- The remaining integral over the positive cone equals `1 / centralWishartDensityConstant 0 n` by `centralWishartCoordinateDensity_cone_mass`, which cancels the prefactor.
- Result: survival probability is exactly `exp(-n * x)` for `x ≥ 0`.

This matches `expMeasure (n : ℝ)` which has rate parameter `n` (mean `1/n`). The CDF uniqueness argument via `StieltjesFunction.ext` is valid since both sides are continuous from the right.

## Normalization Non-Circularity

**No problem found.** The proof flow is:
1. `complexWishart_realCoordinates_eq_closedDensity` establishes the density by induction using the Bartlett transport theorem (imported, not assumed here).
2. `lintegral_centralWishartCoordinateDensity = 1` is a **consequence** via `measure_univ = 1` of the pushforward measure.
3. `centralWishartCoordinateDensity_cone_mass` uses step 2 plus the fact that the density vanishes outside the positive cone (by definition via `if_pos`/`if_neg`).
4. The shifted cone probability in step 3 of `actualCentralSquareWishart_shiftedCone_probability` invokes `cone_mass` only after the translation identity `centralCone_candidateIntegral_shift` (imported from cone integral theory) factors out `exp(-n*x)`.

No step assumes what it proves.

## Shifted Cone Containment

**No problem found.** `centralCoordinateShiftedCone_subset_positive` requires `0 ≤ x`: if `A - xI ≻ 0` and `x ≥ 0`, then `A = (A - xI) + xI ≻ 0` since `xI ≽ 0`. This is used to apply `centralWishartCoordinateDensity_on_cone` inside the shifted-cone integral, which is valid.

## Potential Issue: `n = 0` Edge Case in Definitions

**Minor observation, not a bug.** `centralSquareSampleMinimum` requires `hn : 0 < n`, so the `n = 0` case is excluded from the exponential law. However, `centralCoordinatePositiveCone 0` and the density are defined for `n = 0` (yielding the trivial space `Matrix (Fin 0) (Fin 0) ℝ`). The cone integrals and `complexWishart_realCoordinates_eq_closedDensity` handle `n = 0` in the base case. This is consistent: the minimum eigenvalue is undefined for empty matrices, but the measure-theoretic machinery gracefully degenerates.

## Potential Issue: Measurability Coercion

**No concrete problem.** `ENNReal.ofReal` applied to `Real.exp (-(n : ℝ) * x)` is well-defined since the exponential is nonnegative. The cast `(n : ℝ)` is exact. In `actualCentralSquare_minimum_tail`, rewriting through `Measure.map_map` and `Measure.map_apply` requires measurability of `complexSampleGram` and `realCoordinatesOfHermitian`, both supplied by continuity. The set equality via `centralSquareSampleMinimum_threshold` lifts pointwise to preimage equality.

## Circularity Check

**No circularity detected.** The imported results form a DAG:
- Bartlett recursion → closed density (this file)
- Closed density + cone translation → shifted cone probability
- Spectral theorem (deterministic) → threshold equivalence
- Threshold + shifted cone probability → tail formula
- Tail formula → CDF → measure identification

The density does not depend on the minimum-eigenvalue law; the minimum-eigenvalue law depends on the density.

## Variance Convention

**Consistent.** Complex Gaussian entries with variance one per complex component yield the `exp(-trace)` term without additional scaling. The `stdGaussian` on `ComplexSample` matches the `complexWishart` definition. No hidden factor of 2 discrepancy between real and complex variance conventions is present.

---

**Verdict:** No concrete semantic errors identified. All dimensional parameters, strict/non-strict boundaries, normalizations, and logical dependencies are internally consistent and consistent with the stated claims.

[需人工审查]
