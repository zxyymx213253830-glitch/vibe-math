## P4 Adversarial Review

### Source 1: `PowerExponentialIntervalMoments.lean`

**Mathematical gap (measure support vs. integral domain).** The density `|y|^d * exp(-y)` is defined on all of `ℝ`, but the measure restricts to `Ioc 0 x`. When `x < 0`, `Ioc 0 x = ∅`, so the measure is zero and all integrals vanish. However, `partialGamma_nat_succ_eq_realInterval` likely assumes a non-degenerate interval `[0, x]` with `x ≥ 0`. The theorem `powerExponentialInterval_integral_pow_eq_partialGamma` includes `hx : 0 ≤ x`, which is correct—but the finiteness and integrability theorems lack this hypothesis. For `x < 0`, `isFiniteMeasure` still holds trivially, but invoking `integrableOn_Icc.mono_set Ioc_subset_Icc_self` when `Ioc 0 x = ∅ ⊆ Icc 0 x = ∅` is vacuously fine. **No actual gap**, but the asymmetry between unconditional finiteness/integrability and conditional moment evaluation should be noted as a design fragility.

**Potential coercion issue.** In `integral_withDensity_eq_integral_toReal_smul`, the density involves `ENNReal.ofReal (...)` then `toReal`. The step `ENNReal.toReal_ofReal (by positivity)` requires `0 ≤ |y|^d * exp(-y)`, which holds. This is correct.

**Dependency signature assumption.** `partialGamma_nat_succ_eq_realInterval` is imported and treated as given. Its exact statement must assert equality for the specific integral form `∫ y in 0..x, y^n * exp(-y)` matching the partial Gamma definition used. If the imported result uses a different convention (e.g., lower incomplete gamma `γ(s,x) = ∫₀ˣ t^{s-1} e^{-t} dt` vs. an unnormalized variant), the index shift `d+k+1` could be off by one. **This is a concrete semantic mismatch risk**: verify that `partialGamma (n : ℂ) x` in the dependency corresponds to `∫₀ˣ t^{n-1} e^{-t} dt` (standard) or `∫₀ˣ t^n e^{-t} dt` (shifted). The proof uses it with argument `(d+k+1 : ℕ) : ℂ`, suggesting the shifted convention; if the library uses the standard convention, this is **off-by-one**.

### Source 2: `ActualCentralTwoColumnMaximum.lean`

**Set equality `P ∩ S = R ∩ O`—boundary handling.** The proof expands to `u ≤ x ∧ 0 < v ∧ v < u ↔ (0 < u ∧ u ≤ x) ∧ (0 < v ∧ v ≤ x) ∧ v < u`. The forward direction derives `0 < u` from `lt_trans hv0 hvu` (i.e., `0 < v < u`), which is valid. The reverse derives `v ≤ x` from `le_trans hvu.le hux` (i.e., `v ≤ u ≤ x`), valid. **No gap.**

**Indicator/withDensity rewriting.** `lintegral_withDensity_eq_lintegral_mul _ hW (hG.indicator hO)` requires the second argument to be measurable and non-negative or integrable in the appropriate sense. `hG.indicator hO` is measurable (`hG` measurable, `hO` measurable set). The lemma typically requires `AEMeasurable` or full measurability plus a non-negativity condition. Since `G ≥ 0` pointwise (it's `ENNReal.ofReal` of a square), the indicator is also `≥ 0`. **No gap.**

**Division by factorial constant.** `eq_div_iff hC.ne'` requires `(d! * (d+1)!) ≠ 0` in `ℝ`. Since factorials are positive naturals, their casts are nonzero. **No gap.**

**Measurability of eigenpair map.** `measurable_twoColumnMatrixEigenpair.comp measurable_complexSampleGram` assumes both components are separately proven measurable in dependencies. Treated as given per instructions.

**Critical dependency: `ordered_square_gap_moment_identity`.** This returns a pair `(hg.1, hg.2)` where `hg.1` asserts non-negativity of some real quantity (used in `Complex.norm_of_nonneg`) and `hg.2` is an integral identity. The proof applies `hg.2` to rewrite the LHS of `max_weighted_ordered_integral` into a two-moment determinant form. If `ordered_square_gap_moment_identity` requires additional hypotheses (e.g., finite measure, which is available via the instance, or specific integrability beyond what's passed), there would be a gap. The explicit arguments passed are the two integrability proofs, which matches the expected signature pattern. **No internal gap**, but this is the linchpin dependency.

**`Complex.norm_of_nonneg` usage.** Applied to `hg.1` (a real non-negativity claim) and `hC` (factorial product non-negativity). This coerces reals to complexes and asserts `‖(r : ℂ)‖ = r` when `r ≥ 0`. Standard. **No gap.**

### Summary of Problems Only

1. **Semantic mismatch risk (Source 1):** Verify `partialGamma` convention in the imported library. If it uses the standard `∫₀ˣ t^{s-1} e^{-t} dt` definition, passing `d+k+1` computes `∫₀ˣ t^{d+k} e^{-t} dt`, which matches the goal `∫ y^k · |y|^d · e^{-y}` only if `|y| = y` on `(0,x]` (true given `hx : 0 ≤ x`). **Actually consistent upon reflection**—no gap, but fragile.

2. **No other mathematical gaps detected.** All measure-theoretic rewritings, set equalities, and coercions are internally justified by the stated hypotheses.
