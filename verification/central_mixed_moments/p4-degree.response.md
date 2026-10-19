# P4 Direct Issues-Only Review

## Empty Cases (n=0 or d=0): No Issues

- **n=0**: `Fin 0` is empty, matrices are 0×0. Mathlib's `det_one` gives 1, `Fintype.card_fin 0 = 0`, so `P = (X + 1)^d` and `Q = 1`. Degree is `0 = d*0`. All theorems hold.
- **d=0**: `P = 1`, `Q = 1`. Degree is `0 = 0*n`. All theorems hold.
- **n=d=0**: Trivially consistent.

No missing edge cases here.

## Lost Terms / Cancellation: No Issue in Degree Bound

`complexGaussianIntegratedPolynomial_natDegree_le` uses `natDegree_sum_le_of_forall_le`, which is valid regardless of cancellation. The comment "coefficientwise linear integration may cancel terms but cannot increase degree" is correctly formalized. No issue.

## Top Coefficient Reasoning: No Circularity

The chain is acyclic:
1. `shiftedGramPolynomialInX_coeff_top` proves coeff at `d*n` equals `1` using only mathlib assets (`coeff_det_X_add_C_card`, `coeff_pow_of_natDegree_le`) — no moment functional involved.
2. `complexGaussianPolynomialMoment_one` proves `L(1) = 1` directly from definition.
3. `centralMinimumUnivariatePolynomial_coeff_top` combines these via `complexGaussianIntegratedPolynomial_coeff`.
4. `natDegree_eq_of_le_of_coeff_ne_zero` closes exact degree.
5. `monic` follows from exact degree + top coefficient.

No step assumes what it's proving. The moment functional is applied *only after* the leading coefficient is identified as `1` in the source polynomial ring.

## Potential Issue: `coeff_pow_of_natDegree_le` Application

In `shiftedGramPolynomialInX_coeff_top`, the call `Polynomial.coeff_pow_of_natDegree_le (m := d) hb` requires that `hb` establishes `natDegree ≤ n` for the base polynomial. This is exactly what `natDegree_det_X_add_C_le` provides (after rewriting with `hM` and `card_fin`). **Correct.**

The subsequent `rw [hc, one_pow] at hp` substitutes the top coefficient of the determinant (= `det 1 = 1`) into the power formula. **Correct.**

## Potential Issue: `add_comm` Rewrite Target

`simpa only [shiftedGramPolynomialInX, add_comm]` relies on `shiftedGramPolynomialInX` being defined as `(C + X)^d` rather than `(X + C)^d`, needing `add_comm` to match the `det (X·1 + C)` form from mathlib. If the definition already matches, `add_comm` is a no-op. Either way, **not a bug**, just potentially redundant.

## `complexGaussianIntegratedPolynomial_coeff`: Sum Manipulation

The proof uses `finsetSum_coeff` then `sum_eq_single k`:
- Off-diagonal terms vanish by `coeff_monomial` when `b ≠ k`. ✓
- The `hk ∉ support` case correctly deduces `P.coeff k = 0` via `mem_support_iff`. ✓

**No issue.**

## `complexGaussianPolynomialMoment_one`: Tautological Given Prior Work

This is stated as proven "earlier." If the functional sends `1 ↦ 1` by axiom/prior theorem, this `simp` proof is fine. If it depends on Gaussian integration normalization, that dependency is external to this file. **No local issue; correctness inherited from upstream.**

## Summary

| Check | Status |
|-------|--------|
| Lost terms/cancellation | Safe — sum degree bound handles cancellation |
| Top coefficient identification | Correct — pure polynomial algebra, no moment circularity |
| Empty cases n=0, d=0 | Handled correctly by mathlib conventions |
| Circular moment/leading-coeff reasoning | None — clean separation |
| Mathlib asset usage | Correct parameterization |
| Exact degree + monic closure | Valid given le + coeff≠0 |

**Verdict: No blocking issues found.** The proof structure is sound and non-circular. The human-review flag applies only to the probability-model interpretation (external to this file), not to the polynomial-algebra mechanics formalized here.
