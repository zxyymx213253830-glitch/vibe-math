## P4 Adversarial Review

### FiniteSpectrumOffsetInverseRate.lean

**1. Missing domain condition in `positiveModeOffsetError_nonneg_le_inverse` (Mathematical Gap)**

The theorem assumes `hx : 0 ≤ x` and `hr : 0 < r`, then splits on `hp : 0 < x`. In the positive branch, the proof uses `x⁻¹` freely and applies `Real.log_mul hr.ne' hp.ne'`, which requires `x ≠ 0` (satisfied). However, the final bound is `r⁻¹ * x⁻¹`. When `x = 0` (the `hz` branch), the conclusion reduces to `0 ≤ 0 ∧ 0 ≤ 0` via simplification. This is only valid if `positiveModeOffsetError 0 r = 0` **and** the definition handles `x⁻¹` at zero gracefully (likely through `if_pos`/`if_false` guards in `positiveSpectrumLog`). If `positiveSpectrumLog` does not explicitly return `0` when its argument is `0`, this produces a junk value rather than a mathematical truth. The proof depends entirely on definitional unfolding that isn't shown; verify that `positiveSpectrumLog` has an explicit `if 0 < x` guard making the `x = 0` case definitionally zero, not just provably zero under additional unstated assumptions.

**2. Implicit coercion in sum bound (Minor)**

In `finiteSpectrumOffsetError_nonneg_le_min_inverse`, the bound uses `(Fintype.card ι : ℝ)`. The coercion is fine, but the hypothesis `hmin : ∀ i, 0 < x i → a ≤ x i` combined with `ha : 0 < a` means that when all `x i = 0`, the bound becomes `card(ι) * r⁻¹ * a⁻¹ > 0` while the LHS is exactly `0`. This is mathematically correct but wasteful—the bound doesn't tighten to `0` when the spectrum is identically zero because `a⁻¹` remains. Not a gap, but the `hmin` hypothesis is vacuously satisfied for any `a > 0` when all eigenvalues vanish, making the quantitative content degenerate.

---

### ActualSingularOffsetRate.lean

**3. Index identification via `Fin.ext` + `omega` is fragile (Mathematical Gap)**

The step `have he : i = i₀ := Fin.ext (by rw [← hr] at hi₀; omega)` identifies the user-supplied index `i` (satisfying `i.val + 1 = min m r`) with the existentially-produced `i₀` from `exists_actualCorrelated_smallest_positive_coordinate`. This works **only if** `hi₀` states `i₀.val + 1 = min m (fromRows B M).rank` and `hr` lets you rewrite. But `hi` constrains `i : Fin (Fintype.card (Fin n))`, meaning `i.val < n`. The `omega` call must also confirm that both indices live in the same `Fin n` type. If `exists_actualCorrelated_smallest_positive_coordinate` returns `i₀ : Fin p` or `Fin m` (depending on how eigenvalues are indexed), this `Fin.ext` is a **type error masked by coercion**, not a valid identification. Verify that `i₀` has type `Fin (Fintype.card (Fin n))` specifically.

**4. AE filter intersection assumes compatible null sets (Potential Gap)**

`filter_upwards [hMin, actualCorrelatedRank_eq_generic_ae B M]` intersects two AE conditions. This is valid only if both are stated over the **same** measure space `(ComplexSample (m := m) (n := p), stdGaussian _)`. If `actualCorrelatedRank_eq_generic_ae` is proved for a different parameterization or if `hMin` carries implicit type-class instances that don't unify, the intersection isn't justified. Check that both lemmas explicitly quantify over `stdGaussian (ComplexSample (m := m) (n := p))` with identical type parameters.

**5. `integral_mono_ae` requires nonnegativity of integrands (Assumption Check)**

The application `integral_mono_ae hErrI (hI.const_mul (((n : ℝ) * t⁻¹)^2)) hBound` needs the dominating function `((n : ℝ) * t⁻¹)^2 * ((actualCorrelatedEigenvalue B M i z)⁻¹)^2` to be AE-nonnegative. Since it's a square times a positive scalar, this holds—but only if `(actualCorrelatedEigenvalue B M i z)⁻¹` is defined (i.e., the eigenvalue is nonzero) on the support of `hMin`. The hypothesis `hz.1` from `hMin` should guarantee `0 < actualCorrelatedEigenvalue B M i z`, making inversion safe. Confirm that `hMin`'s second component `hz.2` (used as `hmin` in the finite-spectrum lemma) actually provides the strict positivity lower bound needed, not merely `≤`.

**6. Definitional unfolding of `R` in `pow_le_pow_left₀` (Minor)**

`simp only [Fintype.card_fin, hE] at hb` reduces `hb.2` to a bound involving `n`, but the subsequent `pow_le_pow_left₀ hb.1 hb.2 2` requires `hb.1 : 0 ≤ ∑ ...` and `hb.2 : ∑ ... ≤ n * t⁻¹ * (eigenvalue)⁻¹`. The factor `n` comes from `Fintype.card_fin n`; ensure this is literally `n : ℝ` after coercion, not `(Fintype.card (Fin n) : ℝ)` stuck in unreduced form, or `mul_pow` won't close the goal syntactically.
