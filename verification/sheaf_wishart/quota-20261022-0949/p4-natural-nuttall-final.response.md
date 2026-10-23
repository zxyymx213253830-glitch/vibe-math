# P4 Adversarial Review

## BesselINaturalSeries.lean

**1. Missing summability proof in `modifiedBesselI_nat_eq_factorialSeries`.**
The theorem rewrites `regularizedHGFun` as a `tsum` via `FormalMultilinearSeries.ofScalars_sum_eq`, then applies `tsum_congr`. However, the factorial series on the right is only conditionally asserted equal to the regularized hypergeometric function; no independent `Summable` proof for the factorial series is provided. If `regularizedHGFunSeries` carries a summability side-condition (common for 0F1 at general complex arguments), this rewrite is incomplete. The `ring` finish after `field_simp` does not discharge analytic convergence. This is an **actual gap** unless `Complex.regularizedHGFun` is defined as the tsum unconditionally (making the equality definitional, but then the intermediate `change` step is suspicious).

**2. Coercion commutation with infinite sum in `modifiedBesselI_nat_ofReal_eq_realSeries`.**
`Complex.ofReal_tsum` requires `Summable` of the real series. No real-domain summability proof is given before commuting `ofReal` past `∑'`. The factorial denominators are positive, so this likely holds, but it is **not proved** in this file.

**3. Division by zero risk in `nuttallQIntegrand_eq_evenRadialKernel`.**
`field_simp [h2]` handles `(2:ℂ)^q ≠ 0`, but the definition of `noncentralChiEvenRadialKernel` (unfolded here) may itself contain factorial or power denominators depending on `r`. If `r = 0` and `q = 0`, terms like `r^(2*q+1)` vanish harmlessly, but if the kernel definition involves `r`-dependent divisions not guarded here, the pointwise equality could fail on a measure-zero set. Minor, but worth flagging given the integration downstream.

---

## NaturalNuttallNormalization.lean

**4. `integral_tsum_of_summable_integral_norm` hypothesis mismatch.**
This theorem requires that each term is integrable (`hFint`) **and** that the sum of integral-norms is summable (`hsum_norm`). Both are provided. However, `hnorm` asserts `(∫ r, ‖chiEvenPoissonTerm q a r n‖ ∂μ) = evenPoissonWeight a n` using `abs_of_nonneg` justified by `positivity`. The `positivity` tactic inside `filter_upwards` is applied pointwise for `r ∈ Ioi 0`; this works only if `chiEvenPoissonTerm` is manifestly nonnegative for all such `r`. Given the term includes `r^(2*(n+q)+1) * exp(-r^2/2)` and Poisson weights, this is true, but the `unfold` + `positivity` chain is fragile—if the upstream definition changes sign structure, this silently breaks. **Not a current gap**, but a maintenance risk.

**5. `integrableOn_noncentralChiEvenRadialKernel` uses circular logic.**
`Integrable.of_integral_ne_zero` concludes integrability from the integral being nonzero. But `noncentralChiEvenRadialKernel_integral_eq_one` already assumed/proved the integral equals 1, which **presupposes** the integral exists (i.e., the function is integrable). If the integral theorem was proved without establishing integrability first (it uses `integral_tsum_of_summable_integral_norm`, which produces an integrable sum), then this is fine. But if `integral_eq_one` was stated as a raw `∫` equation that Lean interprets as 0 when non-integrable, the reasoning is circular. Check whether Mathlib's `∫` notation returns 0 for non-integrable functions; if so, proving the integral equals 1 does establish integrability, making this OK.

**6. Parameter `a : ℝ` unrestricted—no positivity assumption.**
The Poisson weight `evenPoissonWeight a n` uses `a^2/2`, so negative `a` is fine. But `nuttallQ_succ_self_zero` concludes `(a:ℂ)^q`, and downstream `OneColumnNuttallNormalization` substitutes `a = Real.sqrt (2*lambda)`. The current file's theorems hold for all `a : ℝ`, which is correct, but note that `noncentralChiEvenRadialKernel` likely originates from a chi-distribution context where `a ≥ 0` is physically meaningful. The formalization correctly avoids assuming this, but the imported `noncentralChiEvenRadialKernel_eq_poissonMixture` should be checked for hidden `0 ≤ a` preconditions.

---

## OneColumnNuttallNormalization.lean

**7. `Nat.sub_add_cancel` requires `1 ≤ t`, but `t - 1` when `t = 1` gives `q = 0`.**
`oneColumnZero` sets `q = t - 1` and calls `nuttallQ_succ_self_zero (t-1)`. When `t = 1`, this is `nuttallQ_succ_self_zero 0`, i.e., `nuttallQ 1 0 a 0 = a^0 = 1`. This is consistent, but verify that `nuttallQ` at index `(1, 0)` is actually defined and matches the Bessel series at `q = 0`. No mathematical gap, but a boundary sanity check.

**8. `Complex.norm_of_nonneg` applied to `Real.sqrt (2*lambda)`.**
Requires `0 ≤ Real.sqrt (2*lambda)`, which holds by `Real.sqrt_nonneg`. Then `‖(sqrt(...):ℂ)^(t-1)‖ = (sqrt(...))^(t-1)` as a real number. Correct, but note the denominator in the final expression is `(Real.sqrt (2*lambda))^(t-1)` as a **real** number, while the numerator involves a complex norm. The division is real, matching the CDF candidate type. No gap.

**9. Dependency on external normalization theorems.**
`theorem1OneColumnCandidate_eq_normalizedNuttallQ` and `theorem2OneColumnCandidate_eq_normalizedNuttallQIncrement` are imported. Their hypotheses include `oneColumnZero_ne t ht lambda hl`, which requires `0 < lambda`. If those upstream theorems additionally require rank/fullrow conditions specialized to `Fin 1`, verify the `1 ≤ t` and `omega` proofs match exactly. Signature alignment question, not a math gap unless mismatched.
