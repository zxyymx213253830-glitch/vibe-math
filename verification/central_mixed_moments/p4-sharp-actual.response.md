# P4 Concrete Issues Audit: Central Minimum Hard-Edge Coefficient

## 1. One-Sided Filter Mismatch in `analytic_positive_factor` (Critical)

**File:** `CentralMinimumSharpOrder.lean`, `centralMinimumCDFContinuation_positive_factor`

**Issue:** The analytic germ factorization (`exists_eventuallyEq_pow_smul_nonzero_iff`) requires a **two-sided** neighborhood filter `𝓝 0`, but you only supply right-sided positivity (`𝓝[>] 0`) and a right-sided log limit. Analyticity at 0 gives you the germ, but the *positivity* of the factor `H(0) > 0` needs the function to be positive on a full neighborhood, not just the right side.

**Concrete fix required:** You must either:
- Prove `centralMinimumCDFContinuation_pos_two_sided : ∀ᶠ x in 𝓝 0, 0 < ...` (impossible if CDF is genuinely piecewise), OR
- Use a separate argument that for an analytic function with known zero order `k = d+1` (from the right-sided log limit + uniqueness), the leading Taylor coefficient `iteratedDeriv k G 0 / k!` has the same sign as the right-sided values. This bridges right-sided positivity to `H(0) > 0` without assuming two-sided positivity of `G`.

The current code silently passes `pos_right` into a lemma that likely expects two-sided input or internally constructs `H` via division by `x^k`, which is only valid where `x ≠ 0`. Check the exact statement of `analytic_positive_factor_of_log_exponent`—if it assumes `∀ᶠ x in 𝓝 0, 0 < G x`, this is unsound for your actual CDF continuation.

---

## 2. Log Exponent Order Identification: Uniqueness vs. Assumption (Critical)

**File:** `CentralMinimumSharpOrder.lean`, `centralMinimumCDFContinuation_log_exponent` → `centralMinimumCDFContinuation_derivatives_vanish`

**Issue:** You correctly note "not assuming limit from log ratio alone for nonanalytic functions." However, the chain in `derivatives_vanish` uses `analytic_order_of_positive_log_exponent` which identifies the analytic order `k` with the log limit `d+1`. This is valid **only because** you already have analyticity at 0. But the log limit is computed via `actualCentralMinimumCDF_all_diversity` which is a statement about the **actual** (piecewise) CDF on `𝓝[>] 0`.

**Concrete risk:** If `actualCentralMinimumCDF_all_diversity` proves `log F / log x → d+1` using measure-theoretic bounds that don't account for the analytic continuation's behavior on `x < 0`, the identification `order = d+1` is still correct (since analytic order is determined by right-sided limit for analytic functions), but the **dependency direction** in your proof may be circular or rely on an unstated lemma that "right-sided log limit of analytic function = analytic order." Verify `analytic_order_of_positive_log_exponent` doesn't assume the order to prove the limit equals the order.

---

## 3. Off-by-One in Finite Sum Range (High)

**File:** `CentralMinimumFiniteHardEdgeCoefficient.lean`, `centralMinimumFiniteHardEdgeCoefficient`

**Issue:** The sum is over `Finset.range (d+2)`, i.e., `i ∈ {0, 1, ..., d+1}`. The polynomial degree of `centralMinimumRealPolynomial d (n+1)` should be verified. If `P(x)` has degree `≤ d+1`, then `P.coeff(d+1-i)` is accessed for `i=0` giving `coeff(d+1)`, which is fine. But:

- When `i = d+1`, you access `P.coeff(0)` — fine.
- The factorial `(d+1-i).factorial` when `i = d+1` gives `0.factorial = 1` — fine.
- **But:** does `P.coeff j` return 0 for `j > deg P`? In Mathlib, yes. So if the polynomial degree is actually `d` (not `d+1`), then the `i=0` term vanishes and you have a spurious leading term. **Verify the exact degree** of `centralMinimumRealPolynomial d (n+1)`. An off-by-one here propagates directly to the coefficient value.

---

## 4. Sign Error Risk in Convolution/Leibniz Formula (High)

**File:** `CentralMinimumFiniteHardEdgeCoefficient.lean`, `centralMinimumHardEdgeCoefficient_eq_finite`

**Issue:** The prefactor is `-massinv / (d+1)!`. The sum contains `(-N)^i` where `N = n+1`. The Leibniz rule for `iteratedDeriv (d+1) [exp(-Nx) · P(x)]` at 0 gives:

```
∑_{i=0}^{d+1} C(d+1,i) · (D^i exp(-Nx))|₀ · (D^{d+1-i} P)|₀
= ∑ C(d+1,i) · (-N)^i · (d+1-i)! · P.coeff(d+1-i)
```

Then `G(x) = 1 - massinv · exp(-Nx) · P(x)`, so `G^{(d+1)}(0) = -massinv · [above sum]` (since the constant 1 vanishes for `d+1 ≥ 1`). Then divide by `(d+1)!`.

**Concrete check:** Your definition has `-(massinv) / (d+1)! * SUM`. This matches `-massinv · [Leibniz] / (d+1)!`. **However**, verify that `iteratedDeriv_exp_mul_polynomial_zero` in your library produces exactly `∑ C(k,i)(-N)^i (k-i)! coeff(k-i)` and not `∑ C(k,i)(-N)^{k-i}...` (index reversal). A flipped convention in that lemma would invert the sign pattern.

---

## 5. Factorial Type Coercion Consistency (Medium)

**File:** All three files.

**Issue:** Mixed use of `(d+1 : ℕ) : ℝ`, `((d+1).factorial : ℝ)`, and implicit coercions in `choose`. Specifically:
- `centralMinimumFiniteHardEdgeCoefficient`: `((d+1).choose i : ℝ)` — ensure `Nat.choose` coercion matches the real binomial in any analytic lemmas used.
- `(-((n+1 : ℕ) : ℝ))^i` — the base is coerced before negation and exponentiation. This is correct but fragile; if any lemma expects `(-(n+1 : ℝ))^i` vs `(-1)^i * (n+1)^i`, associativity matters for even/odd parity.

**No bug confirmed**, but audit all `norm_cast` / `push_cast` steps in the `ring` tactic at the end of `eq_finite`. If `ring` closes it, coercion is consistent, but double-check that `iteratedDeriv_mul_const_field` handles the `ℝ`-cast of natural number constants correctly.

---

## 6. Missing Classical Simplified Prefactor Identity (Acknowledged, Not a Bug)

You explicitly state: "classical simplified factorial coefficient identity and original general T4 prefactor NOT proved." This is fine for P4 compliance—the finite formula stands on its own. No action needed, but ensure no downstream file imports this and assumes the classical form.

---

## 7. Human Review Tags

All three files carry `[需人工审查]`. Per P4 standards:
- **File 1:** Reviewer must verify the one-sided → two-sided analytic factor bridge (Issue 1 above).
- **File 2:** Reviewer must confirm `analytic_power_taylor_coefficient_pos` doesn't internally assume two-sided positivity.
- **File 3:** Reviewer must validate the polynomial degree bound and Leibniz index convention (Issues 3–4).

These cannot be discharged by automation.

---

## Summary of Required Actions

| Priority | Issue | File | Action |
|----------|-------|------|--------|
| **Critical** | One-sided filter vs. two-sided analytic factor | SharpOrder | Add lemma bridging right-limit to leading coefficient sign, or replace `analytic_positive_factor_of_log_exponent` with right-sided variant |
| **Critical** | Log-limit-to-order dependency direction | SharpOrder | Audit `analytic_order_of_positive_log_exponent` for circularity |
| **High** | Polynomial degree vs. sum range off-by-one | FiniteHardEdge | Prove/state exact degree of `centralMinimumRealPolynomial` |
| **High** | Leibniz index/sign convention | FiniteHardEdge | Cross-check `iteratedDeriv_exp_mul_polynomial_zero` statement against manual expansion |
| **Medium** | Cast hygiene | All | Verify `ring` discharges all coercion goals; spot-check one parity case |
