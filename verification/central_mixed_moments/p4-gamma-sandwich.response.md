# P4 Direct Issues: GaussianLeaveOneOutLaw, GaussianLeaveOneOutEvents, CentralMinimumGammaSandwich

Reviewing the 13 new statements across three files for measurability, full-rank handling, model assumptions, and logical gaps. No tools used, no rewrites.

---

## GaussianLeaveOneOutLaw.lean (4 statements)

**1. `selectedColumnFirstEquiv_zero` / `selectedColumnFirstEquiv_succ`**
- **Issue**: `finSuccEquiv'` composition is stated but not unfolded. The proof is `simp [selectedColumnFirstEquiv, finSuccEquiv']`. If `finSuccEquiv'` has conditional branches or requires case-splitting on `j = 0` vs `j ≠ 0`, `simp` may silently leave goals or depend on lemmas not in scope. Verify that `finSuccEquiv'` is definitionally transparent for all `j : Fin (n+1)`, including boundary cases `j = 0` and `j = last`. No actual bug visible, but this is a hidden-assumption risk.

**2. `measurable_totalLeaveOneOutEnergy`**
- **Issue (measurability)**: Uses `(measurable_gramInverseProjector_euclidean m n).comp (hB.prodMk hv)`. This requires `gramInverseProjector` to be jointly measurable in both the submatrix and the column vector arguments simultaneously. If `measurable_gramInverseProjector_euclidean` was proved only for fixed-dimension types with product sigma-algebra, confirm the product structure on `Matrix × Vector` matches what `.prodMk` produces. A type mismatch between the domain of `gramInverseProjector` and the codomain of `prodMk` would silently fail at runtime or produce an axiom dependency.
- **Issue (variance/model)**: Implicitly assumes the standard Gaussian measure on `ComplexSample (m := m) (n := n+1)` gives i.i.d. standard complex normal entries. If `ComplexSample` carries a different variance convention (e.g., real/imaginary parts each variance 1 vs total variance 1), the Gamma shape/rate will be wrong. This is not checked here.

**3. `actualLeaveOneOut_energy_law`**
- **Issue (full-rank AE discharge)**: The proof uses `actualFirstColumn_residual_energy_law hn hnm` which itself should require `n < m` (not just `0 < n`). The hypothesis `hnm : n < m` is present, but confirm that `actualFirstColumn_residual_energy_law` does not additionally require a full-rank event assumption that is being smuggled in. The comment says "imported fullrank is ACTUAL arbitrary Gaussian n≤m, not assumed fullrank event" — verify that `actualFirstColumn_residual_energy_law` indeed discharges full-rank almost-everywhere internally rather than taking it as a hypothesis.
- **Issue (measure transport)**: `rw [Measure.map_map hF (measurable_sampleColumnSelection _)]` requires `sampleColumnSelection` to be measurable AND `hF` to be measurable with respect to the pushed-forward sigma-algebra. You have `hF : Measurable F`, but `map_map` needs `AEMeasurable` in some Mathlib versions. Check whether `Measurable` suffices or if you need `.aemeasurable`.
- **Issue (congrArg on measures)**: `congrArg (fun μ => μ.map F)` is applied to a measure equality. This is valid only if `F` is the same function on both sides. Since `F` is defined via `let`, confirm no universe or type-class inference issue causes `F` to differ between the LHS and RHS of `h`.
- **Issue (N≥2 vs one-column)**: The header says "N≥2 here, one-column case already elsewhere." But `hn : 0 < n` allows `n = 1`, giving `N = n+1 = 2`. The case `n = 0` (one column total, zero remaining) is excluded by `hn`. Confirm that `actualFirstColumn_residual_energy_law` does not silently cover `n = 0` and create overlap/contradiction with the "elsewhere" theorem.

---

## GaussianLeaveOneOutEvents.lean (5 statements)

**4. `gramSmallestValue_sample_eq`**
- **Issue**: Pure definitional unfolding. Low risk, but confirm `complexNoncentralSampleSmallestEigenvalue` with `add_zero` actually reduces to `centralGaussianSampleMinimum` without leftover casts or type coercions that `simp` ignores.

**5. `leaveOneOut_preceding_isUnit_ae`**
- **Issue (AE transport)**: Uses `ae_map_iff` to pull back an AE statement through `sampleColumnSelection j.succAbove`. This requires `sampleColumnSelection` to be **bimeasurable** (or at least for the preimage of measurable sets to be measurable and null sets to correspond). You only assert `(measurable_sampleColumnSelection j.succAbove).aemeasurable`. If `sampleColumnSelection` is not injective-a.e. or its inverse is not measurable, `ae_map_iff.mp` can fail. The proof uses `j.succAbove_right_injective` for the `stdGaussian_sampleColumnSelection_law` rewrite, but injectivity alone does not guarantee the sigma-algebra pushforward/pullback equivalence needed for `ae_map_iff`. Verify the exact Mathlib signature of `ae_map_iff` — it typically requires `Embedding` or `Bimeasurable`, not just `Injective + Measurable`.
- **Issue (hidden assumption)**: `complexSample_shiftedGram_isUnit_det_ae` is instantiated with shift `0`. Confirm this lemma does not assume `n ≤ m` strictly or `n < m`; you pass `hnm : n ≤ m`. If the source lemma requires strict inequality, this is unsound.

**6. `totalLeaveOneOutEnergy_eq_residual_ae`**
- **Issue**: Calls `totalColumnResidualEnergy_eq_complex_residual _ hz _`. The second hole `_` is the column index or vector argument. Confirm this is inferable and not ambiguous. If `totalColumnResidualEnergy_eq_complex_residual` requires additional hypotheses (e.g., `IsUnit` of a specific Gram determinant, not just any `hz`), those must be discharged.
- **Issue (model)**: Equates `totalLeaveOneOutEnergy` (defined via explicit projection formula) with `leaveOneOutResidualEnergy` (which may be defined via `gramInverseProjector` or pseudoinverse). These are equal only when the preceding submatrix is full rank. You filter through `leaveOneOut_preceding_isUnit_ae`, which is correct, but confirm `IsUnit det` is exactly the condition `totalColumnResidualEnergy_eq_complex_residual` needs — not merely nonzero determinant, but invertibility in the ring sense (for `ℂ` these coincide, but Mathlib's `IsUnit` on `ℂ` may have edge cases at 0).

**7. `actualLeaveOneOut_minimum_le_energy_ae`**
- **Issue**: Uses `gramSmallestValue_le_leaveOneOut_energy _ j`. Confirm this lemma holds for **all** matrices or only full-rank ones. If it requires full rank of the **full** `(n+1)`-column matrix (not just the preceding `n` columns), then filtering through only `totalLeaveOneOutEnergy_eq_residual_ae` (which ensures the preceding submatrix is full rank) is insufficient. The minimum eigenvalue of the full Gram matrix could behave differently if the full matrix is rank-deficient even though the submatrix is not.

**8. `actualLeaveOneOut_exists_energy_le_dimension_minimum_ae`**
- **Issue**: `ae_all_iff.mpr (fun j => ...)` converts a pointwise-AE statement into an AE-forall statement. This is valid for **finite** index types (`Fin (n+1)`), but confirm `ae_all_iff` is imported and applies to `Fin (n+1)` without requiring `Countable` or other typeclass instances that might be missing.
- **Issue**: `exists_leaveOneOut_energy_le_dimension_mul_minimum` is a deterministic algebraic statement about matrices. Confirm it does not carry side conditions (e.g., positivity of minimum, non-degeneracy) that would fail on a measure-zero set not captured by `hall`.

---

## CentralMinimumGammaSandwich.lean (4 statements)

**9. `actualLeaveOneOut_energy_CDF`**
- **Issue (ENNReal.toReal)**: Uses `cdf_eq_real` and later `change ... .toReal = ... .toReal`. Confirm that both sides are finite (not `⊤`). You have `IsProbabilityMeasure` instance, so the measure of `Set.Iic x` is ≤ 1, hence `.toReal` is lossless. This appears fine.
- **Issue (x real, not positive)**: Statement says "All x real." For `x < 0`, `cdf (gammaMeasure ...) x = 0` and `{z | totalLeaveOneOutEnergy j z ≤ x}` should also be empty (energy is nonneg). Confirm `actualLeaveOneOut_energy_law` holds as a measure equality on all of `ℝ`, not just `ℝ≥0`. Pushforward of a measure supported on `ℝ≥0` to `ℝ` is fine, but CDF definitions sometimes branch on sign.

**10. `actualGaussian_minimum_gamma_lower`**
- **Issue (union bound direction)**: Lower bound uses a single column `j = 0`, not a union. Correct: `{min ≤ x} ⊇ {E_0 ≤ x}` because `min ≤ E_0` always. You use AE inequality `min ≤ E_0 a.e.` via `actualLeaveOneOut_minimum_le_energy_ae`. Confirm the AE inclusion `measure_mono_ae` works: you need `{z | min z ≤ x} ⊇ {z | E_0 z ≤ x} \ N` where `N` is null. The `filter_upwards` gives `hz : min z ≤ E_0 z` outside a null set, so `E_0 z ≤ x → min z ≤ x` outside that null set. This is correct.
- **Issue (finiteness for toReal_mono)**: `apply ENNReal.toReal_mono (by finiteness)` — confirm `finiteness` tactic succeeds. The measure of a subset of a probability space is finite, so this should work.

**11. `actualGaussian_minimum_gamma_upper`**
- **Issue (union bound, NOT independence)**: Correctly uses `measureReal_iUnion_fintype_le` (subadditivity), not product/independence. No issue here.
- **Issue (scaling inside CDF)**: The upper bound is `N * cdf(γ)(N*x)`, not `N * cdf(γ)(x)`. Confirm the event inclusion: `∃j, E_j ≤ N*min` gives `{min ≤ x} ⊆ ⋃_j {E_j ≤ N*x}`. This is correct: if `min ≤ x`, then some `E_j ≤ N*min ≤ N*x`. The factor `N` appears both as the union multiplier and inside the CDF argument. This is mathematically correct for the sandwich.
- **Issue (mul_le_mul_of_nonneg_left)**: Uses `Nat.cast_nonneg (n+1)` for `N ≥ 0`. Since `N = n+1 ≥ 1 > 0`, this is fine. But confirm `hj.trans (...)` type-checks: `hj : E_j ≤ N * min z` and you need `E_j ≤ N * x` given `min z ≤ x`. So `N * min z ≤ N * x` by monotonicity. Correct.

**12. `actualCentral_minimum_gamma_sandwich`**
- **Issue (reparameterization d = m-n-1 vs m = d+n+1)**: You set `m := d+(n+1)` so `m - n = d + 1`. The shape parameter becomes `d+1`. Confirm this matches the intended statement: the Gamma distribution should be `Gamma(m-n, 1) = Gamma(d+1, 1)`. The lower bound uses `cdf (gammaMeasure ((d+1 : ℕ) : ℝ) 1) x` which matches. No bug, but the docstring says "GammaCDF_{m-n}" while the code uses `d+1`; ensure `d` is always `m - n - 1 ≥ 0`, i.e., `m ≥ n+1`, which follows from `hnm : n < m`.
- **Issue (conjunction vs separate theorems)**: Returns `⟨lower, upper⟩`. Both rely on `hnm` derived from `omega`. If `d = 0` and `n = 0`, then `m = 1`, `hnm : 0 < 1` holds, but `hn : 0 < n` fails. So `n ≥ 1` is enforced. The sandwich requires `N = n+1 ≥ 2`, consistent with the file header.

---

## Cross-Cutting Priority Issues (Measurability / FullRank / Model / Variance)

| Category | Risk | Location |
|----------|------|----------|
| **Measurability** | `ae_map_iff` with only `Measurable + Injective`, not `Bimeasurable` | `leaveOneOut_preceding_isUnit_ae` |
| **Measurability** | `Measure.map_map` requiring `AEMeasurable` vs `Measurable` | `actualLeaveOneOut_energy_law` |
| **FullRank** | `gramSmallestValue_le_leaveOneOut_energy` may need full-rank of full matrix, not just submatrix | `actualLeaveOneOut_minimum_le_energy_ae` |
| **FullRank** | `IsUnit det` over `ℂ` vs nonzero — confirm equivalence for complex matrices | `totalLeaveOneOutEnergy_eq_residual_ae` |
| **Model/Variance** | `ComplexSample` variance convention never checked against `gammaMeasure` rate parameter | All files |
| **Hidden assumption** | `actualFirstColumn_residual_energy_law` internal full-rank discharge not verified | `actualLeaveOneOut_energy_law` |
| **Boundary** | `n = 0` excluded by `hn : 0 < n`, but `d = 0` allowed; confirm no division-by-zero or empty-matrix edge case in `gramInverseProjector` | Sandwich file |

---

## Summary of 13 Statements

| # | Statement | Verdict |
|---|-----------|---------|
| 1 | `selectedColumnFirstEquiv_zero` | OK pending `finSuccEquiv'` definitional check |
| 2 | `selectedColumnFirstEquiv_succ` | Same |
| 3 | `measurable_totalLeaveOneOutEnergy` | **P4**: product measurability of `gramInverseProjector` domain match |
| 4 | `actualLeaveOneOut_energy_law` | **P4**: `map_map` aemeasurable, full-rank discharge verification |
| 5 | `gramSmallestValue_sample_eq` | OK (definitional) |
| 6 | `leaveOneOut_preceding_isUnit_ae` | **P4**: `ae_map_iff` bimeasurability gap |
| 7 | `totalLeaveOneOutEnergy_eq_residual_ae` | **P4**: `IsUnit` condition sufficiency |
| 8 | `actualLeaveOneOut_minimum_le_energy_ae` | **P4**: full-matrix vs submatrix rank condition |
| 9 | `actualLeaveOneOut_exists_energy_le_dimension_minimum_ae` | OK if `ae_all_iff` fintype resolves |
| 10 | `actualLeaveOneOut_energy_CDF` | OK pending CDF-on-negative-reals check |
| 11 | `actualGaussian_minimum_gamma_lower` | OK |
| 12 | `actualGaussian_minimum_gamma_upper` | OK |
| 13 | `actualCentral_minimum_gamma_sandwich` | OK |

**No independence assumed** — confirmed, union bound only.
**Left-tail asymptotic prefactor** — correctly noted as not proved.
**N≥2** — enforced by `hn : 0 < n`.
