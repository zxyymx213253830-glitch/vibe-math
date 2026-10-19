# P4 Different-Family Review: Concrete Problems Only

I've reviewed the three files against the stated constraints (exact `final3sources`, serial Lean exit 0, standard 3 axioms). Here are the concrete problems found:

## 1. FatouIntegralDivergence.lean

**Line 28 (`rw [he, htop] at hfat`):** After rewriting, `hfat` has type `⊤ ≤ liminf ...`. The subsequent `tendsto_of_le_liminf_of_limsup_le hfat le_top` requires interpreting this as an inequality in `WithTop ℝ≥0∞`. This works, but `le_top` is trivially true for any value, so the limsup bound carries no information—the proof relies entirely on the liminf being ⊤. **This is logically correct** but the limsup argument is vacuous.

**Line 33 (`ofReal_integral_eq_lintegral_ofReal`):** Requires `Integrable (F r) μ` and `∀ᵐ a, 0 ≤ F r a` to convert the real Bochner integral to the ENN integral. The filter_upwards correctly extracts these from `hint`/`hnonneg`. **No problem.**

## 2. LogErrorDivergence.lean

**Line 26 (congr' rewrite):** The algebraic manipulation `r * Real.log (1 + (f a)⁻¹ / r) = r * Real.log (1 + (r * f a)⁻¹)` uses `_root_.mul_inv_rev` and `div_eq_mul_inv`. Concretely: `(r * f a)⁻¹ = f a ⁻¹ * r⁻¹ = (f a)⁻¹ / r`. **Correct**, but `mul_inv_rev` gives `(r * f a)⁻¹ = f a ⁻¹ * r⁻¹`, and you need `mul_comm` implicitly to match the division form. Verify this closes in Lean.

**Line 28 (`simpa only [integral_const_mul]`):** Pulls the constant `r` out of the integral. This requires `r` to be a fixed scalar (which it is, as the integration variable is `a`). **Correct.**

## 3. ActualSquareLogDetError.lean

**Line 20-25 (`htop` by contradiction):** The argument is:
- Assume lintegral ≠ ⊤, so it's finite
- Then `inv` is integrable (via `lintegral_ofReal_ne_top_iff_integrable`)
- But `actualNoncentralRectangular_inverseMinimum_integrable_iff n n hn le_rfl M` gives integrability ↔ `n < n`
- `n < n` is false → contradiction

**Concrete check required:** The iff theorem must apply to the **square** case `m = n` with hypothesis `hnm : n ≤ m` instantiated as `le_rfl`. Verify that `actualNoncentralRectangular_inverseMinimum_integrable_iff n n hn le_rfl M` actually reduces to `n < n ↔ False`. If the rectangular theorem requires strict inequality `n < m` as a hypothesis rather than producing it as the RHS of the iff, this breaks.

**Line 39 (`hpk` computation):** For square `m = n`, we get `m - n + 1 = 1`, so `hpk : (1/2 : ℝ) < 1`. **Correct.**

**Line 57-59 (`Finset.single_le_sum`):** The minimum eigenvalue term is one summand of the full logdet error sum over all `n` eigenvalues. The nonnegativity of each term (log ≥ 0 because argument ≥ 1) is correctly established. **Correct.**

**Line 67-68 (`tendsto_atTop_mono'`):** Uses `minimum ≤ total` to sandwich `r * minimum_log_error ≤ r * Delta`, then divergence of LHS forces divergence of RHS. Requires `hr.le : 0 ≤ r` to preserve inequality direction when multiplying. **Correct.**

---

## Summary of Concrete Action Items

| File | Line | Issue | Severity |
|------|------|-------|----------|
| LogErrorDivergence | 26 | Verify `mul_inv_rev` + implicit commutativity closes | Low (likely works) |
| ActualSquareLogDetError | 20-25 | Confirm `inverseMinimum_integrable_iff n n` produces `n < n` not requiring `n < n` as input | **Critical** |
| ActualSquareLogDetError | 39 | For `m=n`, confirm `hpk : 1/2 < 1` matches `p=1/2` requirement | None (trivial) |

**No other structural or logical errors detected.** The Fatou lemma correctly avoids representing divergent Bochner integrals as infinity; the ENN conversion is guarded by eventual integrability/nonnegativity. The model specification (`complexSampleMatrix = (real + i*imag)/√2`) is external to these files but assumed consistent per your review constraint.
