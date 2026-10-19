# Review of `ProbabilityTailRealMoments.lean` and `NoncentralInverseMinimumRealMoments.lean`

## 1. ProbabilityTailRealMoments — Layer Cake and Real Weights

**Layer cake Fubini (`lintegral_rpow_eq_realWeightedProbabilityTail`)**
- The identity $\int_0^u p t^{p-1} dt = u^p$ for $p > 0$ is correctly justified by `intervalIntegrable_rpow'` with exponent $p - 1 > -1$. This handles the near-zero singularity when $0 < p < 1$ properly: $t^{p-1}$ is unbounded but integrable, dominated by an $L^1$ real power, not a constant. No issue here.
- The use of `lintegral_comp_eq_lintegral_meas_le_mul` (the abstract layer cake / Fubini theorem) requires the weight $g(t) = p t^{p-1}$ to be nonnegative on `Ioi 0`, which is discharged by `mul_nonneg hp.le (Real.rpow_nonneg ...)`. Correct.
- **Potential concern:** The application of `lintegral_comp_eq_lintegral_meas_le_mul` also requires an integrability condition on $g$ over intervals $(0, u)$. You supply `intervalIntegrable_rpow'.const_mul p`. Verify that this API indeed provides `IntervalIntegrable (fun t => p * t^(p-1)) volume 0 u` for all $u > 0$ under the sole hypothesis $p > 0$ (i.e., $p - 1 > -1$). If mathlib's `intervalIntegrable_rpow'` requires the upper bound to be finite or imposes conditions at 0 beyond $p - 1 > -1$, this could be a gap. Given your note "Generic mathlib integral_rpow/intervalIntegrable_rpow verified pinned API," this is likely fine, but a human should confirm the exact statement of `intervalIntegrable_rpow'` covers the open-at-0 interval via the `hG` reduction.

**Near-zero integrability (`realWeightedProbabilityTail_integrableOn_near_zero`)**
- Bounding `probabilityTail μ f t ≤ 1` to get $|p t^{p-1} \cdot \text{tail}| \leq p t^{p-1}$ on `Ioc 0 4` is correct.
- `.mono'` for `IntegrableOn` requires both domination and strong measurability. You provide `(measurable_realWeightedProbabilityTail ...).aestronglyMeasurable`. Correct.
- The norm simplification `abs_of_nonneg` using `mul_nonneg hw0 (probabilityTail_nonneg ...)` is valid. No issue.

**Two-sided threshold (`integrable_positiveRealPower_iff_two_sided_power_tail`)**
- Splitting `Ioi 0 = Ioc 0 4 ∪ Ioi 4` and discharging the near-zero part is clean.
- **Sandwich comparison:** You compare against $t^{(p-1)-k}$ on `Ioi 4`. The algebraic manipulation `p * t^{p-1} * (c/t^k) = (p*c) * t^{(p-1)-k}` is correct, using `Real.rpow_sub ht0` (valid since $t > 4 > 0$) and `Real.rpow_natCast`. 
- **Critical case $p = k$:** The exponent becomes $(p-1)-k = -1$. The reference to `integrableOn_Ioi_rpow_iff` must handle this: $t^{-1}$ is not integrable on `Ioi 4`, corresponding to $p < k$ being false when $p = k$. Your final `constructor <;> intro h <;> linarith` reduces the goal to exactly `p < (k : ℝ)`. This means the critical case $p = k$ correctly falls into the divergent regime. Confirm that `integrableOn_Ioi_rpow_iff` states non-integrability at exponent $= -1$ (i.e., iff exponent $< -1$, meaning $(p-1)-k < -1 \iff p < k$). If it uses `≤` vs `<` incorrectly, the critical boundary would be wrong.
- **Measurability in sandwich:** Both functions are shown strongly measurable. The nonnegativity filters are correctly constructed. The constants `p*c` and `p*C` are strictly positive by `mul_pos`. No issue.

## 2. NoncentralInverseMinimumRealMoments — Inverse Moments

**Integrability threshold (`actualNoncentralInverseMinimum_realMoment_integrable_iff`)**
- Direct application of the two-sided tail theorem with power $k = d+1$. The tail bounds `actualNoncentralInverseMinimumTail_power_bounds` supply the two-sided $c/t^{d+1} \leq \text{tail} \leq C/t^{d+1}$ for $t \geq 4$. 
- **Zero mean:** No nondegeneracy assumption on $M$ is used. The tail bounds from upstream must hold for arbitrary fixed $M$ including $M = 0$. Your declaration says "All fixed means including ZERO allowed, no mean norm nondegeneracy premise." This is contingent entirely on `noncentralMinimumPower_constants_pos` returning strictly positive $c, C$ even when $M = 0$. If those constants degenerate to 0 as $\|M\| \to 0$, the sandwich fails. Human must verify that `noncentralMinimumPower_constants_pos` does not depend on $\|M\| > 0$.
- **Full rank / inverse at 0:** You note "Inverse 0 nullset already discharged upstream actual full rank." This means `actualNoncentralInverseMinimum` is finite a.e., so $f^p$ is well-defined a.e. Confirm that `ae_of_all _ (actualNoncentralInverseMinimum_nonneg d n M)` truly holds everywhere (or a.e.) without additional rank hypotheses on $M$ beyond the ambient dimension constraints.

**Rectangular reduction (`actualNoncentralRectangular_inverseMinimum_realMoment_integrable_iff`)**
- Writing $n = k + 1$ via `Nat.exists_eq_succ_of_ne_zero` and substituting $m = d + (k+1)$ to reduce to the square-plus-offset form is arithmetically correct given $n \leq m$.
- The threshold becomes $p < d + 1 = m - (k+1) + 1 = m - n + 1$. Matches the declared $p < m - N + 1$. No issue.

**Critical divergence (`actualNoncentralInverseMinimum_realMoment_lintegral_eq_top`)**
- Uses contrapositive: if the ENNReal lintegral is not $\top$, then by `lintegral_ofReal_ne_top_iff_integrable`, the function is Bochner integrable, contradicting the strict threshold $p < d+1$ when $p \geq d+1$.
- **ENNReal.ofReal usage:** Requires $(f(z))^p \geq 0$ a.e., supplied by `Real.rpow_nonneg`. Correct.
- **No Bochner infinity assumption:** You never assert the moment equals some extended value; you only assert the lintegral is $\top$ (diverges). This aligns with "no Bochner infinity/exact moment value/target density assumption." Correct approach.
- The strict positivity $p > 0$ needed for the forward theorem is derived from $p \geq d+1 > 0$. Valid.

**Scalar covariance scaling (`actualNoncentralCovariance_inverseMinimum_realMoment_integrable_iff`)**
- Substitution $z \mapsto \sqrt{v} \cdot z$ with $M' = v^{-1/2} M$ (cast to $\mathbb{C}$). 
- Eigenvalue scaling: `noncentralSampleMinimum_amplitude_scale` gives $\lambda_{\min}(M, \sqrt{v} z) = \sqrt{v} \cdot \lambda_{\min}(M', z)$. Then $(\lambda_{\min})^{-p} = v^{-p/2} \cdot (\lambda_{\min}(M'))^{-p}$.
- **Algebra check:** Your code writes `(v⁻¹)^p * (actualNoncentralInverseMinimum d n M' z)^p`. Since `actualNoncentralInverseMinimum` is defined as $(\lambda_{\min}(M'))^{-1}$, raising to $p$ gives $(\lambda_{\min}(M'))^{-p}$. The prefactor should be $(\sqrt{v})^{-p} = v^{-p/2}$. But you have `(v⁻¹)^p = v^{-p}`. There is a potential discrepancy here: `Real.sq_sqrt hv.le` gives $(\sqrt{v})^2 = v$, and `Real.mul_rpow` splits the power, but verify that the exponent arithmetic yields $v^{-p}$ vs $v^{-p/2}$. Specifically:
  - `rw [Real.sq_sqrt hv.le, _root_.mul_inv_rev]` suggests you're converting $(\sqrt{v})^{-1}$ to something involving $v^{-1}$. Actually $(\sqrt{v})^{-p} = v^{-p/2}$, not $v^{-p}$. If `actualNoncentralInverseMinimum` already takes the reciprocal once, then raising to $p$ gives $(\sqrt{v})^{-p} = v^{-p/2}$. Check whether `(v⁻¹)^p` in your expression should be `v^(-p/2)` or if there's an extra squaring absorbed by `Real.sq_sqrt`. This needs careful human verification of the exponent arithmetic around lines involving `Real.mul_rpow`.
- **Constant factor integrability:** `isUnit_iff_ne_zero.mpr (ne_of_gt (Real.rpow_pos_of_pos (inv_pos.mpr hv) p))` shows $v^{-p} > 0$ hence nonzero. `integrable_const_mul_iff` then factors it out. Correct.
- **Physical M fixed:** The rescaling absorbs $v$ into $M'$, keeping the Gaussian measure standard. The threshold $p < d+1$ is independent of $v$. Correct conceptual approach.

## 3. Axiom and API Verification Notes

- All `#print axioms` commands are present. A human reviewer must inspect the output to confirm no `sorry`, `choice`, or unexpected classical axioms beyond standard mathlib measure theory foundations have been introduced.
- **Fubini/layer cake:** The core dependence is `lintegral_comp_eq_lintegral_meas_le_mul`. Verify this is the standard mathlib Fubini for lintegrals and doesn't carry hidden finiteness assumptions incompatible with $g(t) = pt^{p-1}$ being unbounded near 0.
- **`intervalIntegrable_rpow'`:** Must accept lower limit 0 with exponent $> -1$ on a bounded interval. Standard mathlib `intervalIntegrable_rpow_iff` handles this, but confirm the primed version matches.

## 4. Summary of Required Human Checks

1. **Exponent arithmetic in covariance scaling:** Verify $(v^{-1})^p$ vs $v^{-p/2}$ in `actualNoncentralCovariance_inverseMinimum_realMoment_integrable_iff`. The interaction between `Real.sq_sqrt`, `mul_inv_rev`, and `Real.mul_rpow` needs line-by-line confirmation that the net scalar prefactor is correct.
2. **Tail constants at zero mean:** Confirm `noncentralMinimumPower_constants_pos d n M` yields $c > 0, C > 0$ uniformly, including when $M = 0$.
3. **`integrableOn_Ioi_rpow_iff` boundary:** Verify it states integrability iff exponent $< -1$ (strict), so that the critical case $p = k$ (exponent $= -1$) correctly diverges.
4. **`intervalIntegrable_rpow'` at 0:** Confirm it covers $(0, u]$ with exponent $p-1 > -1$ without requiring boundedness of the integrand.
5. **Axiom listings:** Run and inspect all `#print axioms` outputs.

No rewrites suggested. The structure is sound: real layer cake weights handled via integrable power domination near zero, two-sided polynomial tail comparison with explicit subtraction in the exponent, ENNReal lintegral for divergence at/above critical threshold, arbitrary fixed mean including zero, and scalar variance factored out by rescaling.
