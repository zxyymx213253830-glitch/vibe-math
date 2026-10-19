# P4 Critical Review: Concrete Issues

## Issue 1: Division-by-zero in measurability proof at `r = 0`

In `integral_log_one_add_mul_low_scale`, the measurability argument uses `.div_const r` for **all** `r : ℝ`, including `r = 0`. While the outer limit is `𝓝[>] 0` (so `r > 0` eventually), the `Filter.Eventually.of_forall` wrapper claims the measurability statement holds for every `r`, but `Real.log (1 + r * f a) / r` is undefined at `r = 0`. The dominated convergence theorem (`tendsto_integral_filter_of_dominated_convergence`) requires the integrand family to be defined/measurable for all `r` in some set belonging to the filter, which is satisfied here since `𝓝[>] 0` excludes zero—but the explicit `of_forall` overclaims. This is technically harmless for the DCT application but imprecise as written.

## Issue 2: DCT domination bound direction

The domination step proves `|Real.log (1 + r*f a) / r| ≤ f a` using `Real.log_le_sub_one_of_pos hpos`, yielding `log(1+rf) ≤ rf`. However, this gives `log(1+rf)/r ≤ f` only when `r > 0`. The absolute value handling via `abs_of_nonneg (div_nonneg hlog hr.le)` correctly restricts to `r > 0`, but the envelope `f` must itself be integrable—and the hypothesis provides exactly `hf : Integrable f μ`. **No issue here upon close inspection**, but the nonnegativity of `log(1+rf)/r` relies on both `r > 0` and `f ≥ 0` a.e., which is correctly assembled.

## Issue 3: Pointwise limit composition gap

The pointwise limit invokes `(Real.tendsto_mul_log_one_add_div_atTop (f a)).comp tendsto_inv_nhdsGT_zero`. The library lemma gives `s * log(1 + t/s) → t` as `s → +∞`. Composing with `r ↦ 1/r` as `r → 0⁺` yields `(1/r) * log(1 + f*r) → f`. But the integrand is `log(1+r*f)/r`, which equals `(1/r)*log(1+r*f)`. The `simp` block asserts congruence via `div_eq_mul_inv, inv_inv, mul_comm`, which is algebraically correct. **However**: when `f a = 0`, the library lemma `tendsto_mul_log_one_add_div_atTop 0` states `s * log(1 + 0/s) = s * 0 → 0`, which is fine. When `f a < 0` (measure-zero by `hnonneg`), the pointwise statement need not hold, and `ae_of_all` correctly handles this. No actual bug.

## Issue 4: `finiteSpectrumLogDet` integral swap requires integrability of each summand

In `integral_finiteSpectrumLogDet_low_scale`, the rewrite `integral_finsetSum` requires each `a ↦ Real.log (1 + r * f i a)` to be integrable. The proof cites `integrable_log_one_add_mul μ (f i) (hf i) (hnonneg i) r hr.le`. This helper must establish integrability from `f i` integrable, `f i ≥ 0` a.e., and `r > 0`, using the bound `0 ≤ log(1+rf) ≤ rf`. If that helper only applies for `r ≥ 0` (not strictly positive), the `hr.le` (i.e., `0 ≤ r` from `0 < r`) suffices. **Concrete risk**: if `integrable_log_one_add_mul` requires `r > 0` strictly but is stated with `hr : 0 ≤ r`, there could be a mismatch at `r = 0`—but since the filter is `𝓝[>] 0`, this is moot in context.

## Issue 5: `actualNoncentralGramLogDet_eq_matrix` requires `r ≥ 0`, used at `r > 0`

The equality `he` invokes `actualNoncentralGramLogDet_eq_matrix M r hr.le` where `hr : 0 < r` so `hr.le : 0 ≤ r`. This is consistent. However, this lemma equates the spectral definition `finiteSpectrumLogDet` applied to eigenvalues with the matrix-level `actualNoncentralMatrixLogDet`. **This is the critical bridge**: if the eigenvalue function `complexNoncentralSampleEigenvalue M i z` returns the eigenvalues of the Gram matrix `(I + r M Z)(I + r M Z)*` or of `M Z Z* M*` scaled appropriately, the logdet identity must hold for all `z` (not just a.e.). The `funext` suggests pointwise equality, which is appropriate.

## Issue 6: Target `T = mN + ‖M‖_F²` not addressed

The header states "Closed `T = mN + ‖M‖_F²` NOT claimed proved here; T is independently finite actual trace integral." The limit target is `actualExpectedGramPower M`, which should equal `E[tr(Gram)]`. For the standard complex Gaussian model with variance-1 entries, `E[tr(ZZ*)] = mN` and the noncentral shift contributes `‖M‖_F²`. The review confirms: **this theorem does not prove the closed form**, only that the logdet slope converges to whatever `actualExpectedGramPower M` is defined as. The numerical 40-digit Gamma(1/3) check mentioned in the header is external validation, not part of this formalization.

## Issue 7: Axiom audit request

The `#print axioms` lines are present but their output is not shown. Given the imports (`ActualLogDetMeanBound`, `Complex.LogBounds`), the three-standard-axiom claim (likely `propext`, `Quot.sound`, `Classical.choice`) should be verified against actual output. Use of `classical` in the second theorem explicitly invokes choice.

---

**Summary**: No blocking mathematical errors found. The main concrete concerns are (1) the `of_forall` measurability claim at `r=0` being slightly over-stated despite being filtered away, and (4) ensuring `integrable_log_one_add_mul`'s preconditions match the strict-positivity available from `𝓝[>] 0`. The logical structure correctly chains scalar DCT → finite spectrum sum → matrix logdet without rank assumptions.
