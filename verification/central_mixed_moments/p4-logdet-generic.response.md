# P4 Critical Review

## LogMomentIntegrability.lean

**`integrable_log_of_integrable_inverse_rpow`**: The inequality `|log f| ≤ f + (f⁻¹)^p / p` is correctly derived from the two one-sided bounds `log x ≤ x - 1` and `log x ≤ (x^{-p} - 1)/p` (via `Real.log_le_rpow_div`). The proof combines these as `-log f = log(f⁻¹) ≤ ((f⁻¹)^p - 1)/p ≤ (f⁻¹)^p / p` for the lower bound and `log f ≤ f - 1 ≤ f` for the upper bound. This is valid. No issue.

**`integrable_log_one_add_mul`**: The domination `|log(1 + r*f)| ≤ r*f` uses `log(1+x) ≤ x` for `x ≥ 0` and the fact that `log(1+r*f) ≥ 0` when `r*f ≥ 0`. Correct.

**`integral_log_add_inverse_tendsto`**: The envelope `|log f| + f` and the pointwise bound for `r ≥ 1` require scrutiny. The proof asserts both `neg_abs_le (log(f a)) ≤ log(f a + r⁻¹)` and `log(f a + r⁻¹) ≤ |log(f a)|` via `linarith` from `log_le_log` and `log_le_sub_one_of_pos`. 

- **Concrete issue (domination bound)**: The upper bound `log(f a + r⁻¹) ≤ |log(f a)| + f a` is not adequately justified by the current `linarith` invocation. From `log(f + r⁻¹) ≤ log f + r⁻¹` (which itself needs justification since `log_le_sub_one_of_pos` gives `log x ≤ x - 1`, not directly this additive shift), one would need `r⁻¹ ≤ f a` to conclude, which does not hold generally. The claimed domination `‖log(f a + r⁻¹)‖ ≤ |log(f a)| + f a` for all `r ≥ 1` and `f a > 0` requires a case split: when `f a ≥ 1`, `log(f a + r⁻¹) ≤ log f a + r⁻¹ ≤ log f a + 1 ≤ log f a + f a`; when `0 < f a < 1`, `log(f a + r⁻¹)` could be negative (if `f a + r⁻¹ < 1`) or positive, and the bound needs separate verification. The current `have := le_abs_self (Real.log (f a)); have := abs_nonneg (Real.log (f a)); linarith` does not supply the needed arithmetic — `linarith` cannot deduce `|log(f + r⁻¹)| ≤ |log f| + f` from just `log f ≤ |log f|` and `0 ≤ |log f|` without the actual upper/lower estimates on `log(f + r⁻¹)`.

- **Missing step**: Explicit case analysis on `f a ≥ 1` vs `f a < 1`, or a direct citation of the inequality `|log(x + ε)| ≤ |log x| + x` for `x > 0`, `0 < ε ≤ 1` (which itself needs proof: for `x ≥ 1`, `0 ≤ log(x+ε) ≤ log x + ε/x ≤ log x + 1 ≤ log x + x`; for `x < 1`, use concavity or direct estimation).

## FiniteSpectrumLogDetGrowth.lean

**`integral_finiteSpectrumLogDet_offset_tendsto`**: The identity `∫ log(1 + r*f) - log r = ∫ log(f + r⁻¹)` is correctly proved pointwise using `log(1 + r*f) - log r = log((1+r*f)/r) = log(f + r⁻¹)`. The exchange of finite sum and integral (`integral_finsetSum`) is justified by the individual integrability hypotheses `hi i`. No issue.

**`integral_finiteSpectrumLogDet_prelog`**: The division by `log r → ∞` and the algebraic rearrangement `(card * log r + offset) / log r = card + offset / log r` are correct. No issue.

**Potential mismatch with target statement**: The theorems are stated for abstract indexed families `f : ι → α → ℝ` with pointwise positivity and integrability hypotheses. The connection to eigenvalues of `X^H X` where `X = Z + M` (noncentral Wishart) is not made here — it depends on `HermitianSpectralLogDet` and on establishing that each ordered eigenvalue function `a ↦ λ_i(a)` satisfies the integrability and positivity assumptions. The review prompt states "each ordered eigenvalue is measurable via a previously proved full complex Weyl continuity result, is bounded above by trace and below by minimum" — but the verification that `hf`, `hpos`, `hlog` are actually discharged for the eigenvalue functions in the noncentral Wishart setting is not present in these files. This is a **statement/proof gap**: the prelog theorem assumes `∀ i, Integrable (f i) μ` and `∀ i, Integrable (fun a => Real.log (f i a)) μ`, but whether these hold for the specific spectral functions of `X^H X` under the shifted Gaussian measure is not established here.

## HermitianSpectralLogDet.lean

**`hermitian_det_one_add_smul_eigenvalues`**: Uses unitary diagonalization `A = U D U*`, then `det(I + rA) = det(U(I + rD)U*) = det(I + rD) det(U) det(U*) = det(I + rD)`. The determinant of the diagonal is the product. The final `Equiv.prod_comp` reindexes between `eigenvalues` and `eigenvalues₀`. Correct.

**`gram_real_logdet_eq_spectral`**: Applies the above to `complexGram X` which is Hermitian PSD. The cast from `Real.log (∏ (1 + r*λ_i) : ℝ)` to `finiteSpectrumLogDet` (which is `∑ log(1 + r*λ_i)`) uses `Real.log_prod`. The positivity condition `0 < 1 + r*λ_i` is verified from `λ_i ≥ 0` and `r ≥ 0`. Correct.

**`hermitian_real_logdet_eq_sum_log`**: `Real.log A.det.re = ∑ log λ_i` via `log ∏ λ_i = ∑ log λ_i`. Requires all `λ_i > 0`, which is an explicit hypothesis. Correct.

**No model mismatch in this file** — these are purely deterministic spectral identities.

## Summary of Concrete Issues

1. **LogMomentIntegrability.lean, `integral_log_add_inverse_tendsto`**: The domination proof `‖log(f a + r⁻¹)‖ ≤ |log f a| + f a` has an unjustified `linarith` step. The inequalities fed to `linarith` (`le_abs_self`, `abs_nonneg`) do not imply the required bound without additional case-splitting or a proven auxiliary inequality for `|log(x + ε)|` when `x > 0, 0 < ε ≤ 1`.

2. **FiniteSpectrumLogDetGrowth.lean**: No internal proof errors, but there is a **statement/application gap** — the integrability hypotheses `hf`, `hpos`, `hlog` for eigenvalue functions of the noncentral Gram matrix `X^H X` (with `X = Z + M`) are assumed rather than discharged within these files. The trace bound (for `hf`) and inverse-moment bound (for `hlog`, using the `p < m - N + 1` criterion mentioned in the route) must be supplied elsewhere to close the loop.
