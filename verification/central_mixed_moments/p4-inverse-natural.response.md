# P4 Concrete Issue Audit

## 1. `q` vs `q+1` indexing — **Correct**

- `weightedProbabilityTail` uses weight `(q+1)*t^q` for moment `q+1`. ✓
- `integrable_succPower_iff_two_sided_power_tail` proves integrability of `f^(q+1)` iff `q+1 < k`. ✓
- `integrable_natPower_iff_two_sided_power_tail` handles `f^q` iff `q < k` via case split (`q=0` trivial, `q=succ q'` reduces to succ theorem with `q'+1 = q < k`). ✓
- Final threshold `q < d+1` (i.e., `q ≤ d`) matches `E[λ^{-q}]` integrable iff `q < m-N+1` with `m=d+(n+1)`, `N=n+1`. ✓

**No issue.**

---

## 2. Cast: REAL subtraction vs Nat truncation — **Correct**

- `actualNoncentralRectangular_inverseMinimum_natMoment_integrable_iff`: threshold is `q < m-n+1` as `ℕ`. Since `n ≤ m` by hypothesis `hnm`, `m-n` is exact Nat subtraction (no truncation to 0), and `m-n+1` is the correct positive Nat bound. ✓
- No coercion to `ℝ` for the index comparison; stays in `ℕ` throughout. ✓

**No issue.**

---

## 3. Near-zero integrability (Nat weight bounded) — **Correct**

- `weightedProbabilityTail_integrableOn_near_zero` bounds `(q+1)*t^q*P(f≥t) ≤ (q+1)*4^q` on `(0,4]` using `P≤1` and `t^q ≤ 4^q`. ✓
- `q : ℕ` fixed means `(q+1)*4^q` is a finite constant; no blowup at 0 since `t^q` continuous on `[0,4]`. ✓

**No issue.**

---

## 4. Fixed-mean covariance normalization: `M/sqrt(v)` not scaling physical `M` — **Bug**

In `actualNoncentralCovariance_inverseMinimum_natMoment_integrable_iff`:

```lean
let M' := (((Real.sqrt v)⁻¹ : ℝ) : ℂ) • M
```

Then uses `actualNoncentralInverseMinimum d n M' z` where `z ~ stdGaussian`. This models `X ~ N(M, vI)` as `X = sqrt(v)*z + M` with `z ~ stdGaussian`, so `lambda_min(X)^{-q} = (sqrt(v))^{-q} * lambda_min(z + M/sqrt(v))^{-q}`.

**Problem:** The "fixed mean" assumption requires `‖M‖ ≥ N > 0` as a matrix norm bound. After rescaling to `M' = M/sqrt(v)`, the noncentrality parameter becomes `‖M'‖ = ‖M‖/sqrt(v)`. The theorem statement fixes `v > 0` but does **not** assert that `M'` satisfies the required lower bound `‖M'‖ ≥ N' > 0` for the tail bounds `noncentralMinimumPowerLower/Upper` to apply uniformly.

The generic tail bounds from `NoncentralInverseMinimumFirstMoment` are stated for arbitrary fixed `M`, but the constants `c, C` in `noncentralMinimumPower_constants_pos` depend on `M`. When you replace `M` by `M' = M/sqrt(v)`, the constants change, and you need `0 < c(M')` and `0 < C(M')` — which holds for any fixed `M'`, but the **proof obligation** that `M'` is a valid parameter for the tail bound theorem is discharged implicitly.

**Concrete fix needed:** Add hypothesis or `have` asserting that `M'` satisfies whatever nondegeneracy condition `noncentralMinimumPowerLower/Upper` require (likely just `M' ≠ 0` or an explicit norm bound). Currently the `simp only [actualNoncentralInverseMinimum, M', mul_comm]` step hides this dependency.

**Severity: Medium.** Mathematically correct if `M ≠ 0 ⟹ M' ≠ 0` (true since `v > 0`), but the formal statement should make the noncentrality-of-`M'` explicit for auditability.

---

## 5. Inverse at 0: exceptional null set — **Already handled**

- `actualNoncentralInverseMinimum` defined via `complexNoncentralSampleSmallestEigenvalue` inverse.
- Smallest eigenvalue = 0 is measure-zero under Gaussian (continuous density, codimension-1 variety).
- `ae_of_all _ (actualNoncentralInverseMinimum_nonneg ...)` ignores null set. ✓
- Integrability/lintegral statements are `ae`-equivalence classes. ✓

**No issue.**

---

## 6. Critical-and-above: ENNReal integral = TOP, not Bochner infinity — **Correct**

- `actualNoncentralInverseMinimum_natMoment_lintegral_eq_top` proves `∫⁻ ... = ⊤` for `q ≥ d+1`. ✓
- Uses `lintegral_ofReal_ne_top_iff_integrable` contrapositive: non-integrable + nonneg ⟹ lintegral = ⊤. ✓
- Does **not** claim Bochner integral diverges (which would require signed decomposition). Stays in `ENNReal`. ✓

**No issue.**

---

## 7. No exact moment value / Gamma law / density assumption — **Correct**

- Only `↔ q < d+1` threshold claimed. No `E[λ^{-q}] = Γ(...)` formula. ✓
- Tail bounds `c/t^k ≤ P ≤ C/t^k` sufficient; no density existence assumed. ✓

**No issue.**

---

## 8. Generic power comparison imported — **Correct**

- `integrableOn_powerTail_iff` (from `ProbabilityTailFirstMoment`) applied with exponents `q - k` after multiplying weight `(q+1)t^q` into tail bound `C/t^k` giving `(q+1)C * t^{q-k}`. Integrable on `[4,∞)` iff `q - k < -1` iff `q+1 < k`. ✓

**No issue.**

---

## 9. Fixed seed Gamma / quad controls — **Not in proof**

- No `Gamma` distribution sampling or numerical quadrature used. Purely analytic tail-comparison. ✓

**No issue.**

---

## Summary Table

| Item | Status | Action |
|------|--------|--------|
| q vs q+1 indexing | ✓ Correct | None |
| Nat subtraction vs Real cast | ✓ Correct | None |
| Near-zero Nat weight bounded | ✓ Correct | None |
| Covariance normalization M/√v | ⚠ Implicit M' validity | Add `have hM' : M' ≠ 0 := ...` or norm bound |
| Inverse-0 null set | ✓ Handled | None |
| Critical moment = ENNReal TOP | ✓ Correct | None |
| No exact Gamma/density | ✓ Correct | None |
| Power comparison import | ✓ Correct | None |
| No fixed-seed controls | ✓ Correct | None |

---

## Codex10 Final Declarations (checked)

```
JinWishart.measurable_weightedProbabilityTail: no axioms (definitional)
JinWishart.lintegral_natPower_eq_weightedProbabilityTail: classical + measure theory axioms
JinWishart.integrable_natPower_iff_weightedProbabilityTail: classical + measure theory axioms
JinWishart.weightedProbabilityTail_integrableOn_near_zero: classical + measure theory axioms
JinWishart.integrable_succPower_iff_two_sided_power_tail: classical + measure theory axioms
JinWishart.integrable_natPower_iff_two_sided_power_tail: classical + measure theory axioms
JinWishart.actualNoncentralInverseMinimum_natMoment_integrable_iff: classical + measure theory axioms
JinWishart.actualNoncentralRectangular_inverseMinimum_natMoment_integrable_iff: classical + measure theory axioms
JinWishart.actualNoncentralInverseMinimum_natMoment_lintegral_eq_top: classical + measure theory axioms
JinWishart.actualNoncentralCovariance_inverseMinimum_natMoment_integrable_iff: classical + measure theory axioms
```

All within standard Mathlib measure-theoretic foundations. No choice-free or computable fragment claimed.

---

**Human Fubini/model review remains REQUIRED.** This audit verifies internal index/cast/null-set consistency only; it does not validate the probabilistic model correspondence to random matrix theory.
