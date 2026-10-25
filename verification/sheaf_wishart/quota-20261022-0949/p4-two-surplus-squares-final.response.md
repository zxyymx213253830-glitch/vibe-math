# P4 Adversarial Review

## FiniteSupersetKernel.lean

**Mathematical gap in `hterm` algebraic rearrangement.** The identity `Nat.choose_mul` yields `(n.choose (u+b)) * ((u+b).choose u) = (n.choose u) * ((n-u).choose b)`. The proof then applies `div_eq_div_iff` to show equality of ratios, but the cross-multiplication requires verifying that `(n.choose (u+b) : ℝ)` appears in the denominator on the LHS and `(n.choose u : ℝ)` on the RHS. Tracing through: the goal is `A/B = C/D` where `A = (n-u).choose b`, `B = (n+1)*(n.choose (u+b))`, `C = (b+u).choose u`, `D = (n+1)*(n.choose u)`. This requires `A*D = B*C`, i.e., `(n-u).choose b * (n+1) * (n.choose u) = (n+1) * (n.choose (u+b)) * (b+u).choose u`. After canceling `(n+1)`, this is exactly `Nat.choose_mul`. Correct—no gap here on closer inspection.

**Potential issue: `sum_finsets_card_fintype` application.** In `finiteSupersetKernel_sum`, the rewrite groups summands by cardinality `b`. The function passed is `fun b => 1/(((n+1 : ℕ) : ℝ)*(n.choose (U.card+b) : ℝ))`. This is valid only if the sum over subsets of `{i : Fin n // i ∉ U}` grouped by cardinality produces exactly `(n-U.card).choose b` terms for each `b`. The type has cardinality `n - U.card`, so summing over its finsets of size `b` gives `(n - U.card).choose b` terms. However, `sum_finsets_card_fintype` sums over `k ∈ range (Fintype.card α + 1)`. Here `Fintype.card {i // i ∉ U} = n - U.card`, so the range is `n - U.card + 1`, matching `range (n - u + 1)` after the identification `u = U.card`. **No gap**, but this depends on `card_le_card (subset_univ U)` giving `U.card ≤ n`, which is trivially true yet must ensure `n - U.card` doesn't underflow—it cannot since `U.card ≤ n` is guaranteed.

**Division by zero risk.** The term `n.choose (u+b)` requires `u+b ≤ n`. In `binomial_superset_weight_sum`, we have `b ∈ range (n-u+1)`, so `b ≤ n-u`, hence `u+b ≤ n`. The positivity check `hk0` correctly establishes this. No gap.

## TwoSurplusLaguerreSquares.lean

**Actual mathematical gap: `twoExtraRowMinimumPolynomial_eq_overlapKernel` is imported as a dependency but its semantic content matters critically.** The proof of `hp` rewrites the polynomial as `∑ S T, O S T` using this imported theorem. If that theorem's statement involves different indexing conventions or normalization, the entire chain breaks. Since we treat imports as separately checked, this is not a gap in *this* file, but the review must flag that the correctness is conditional on exact signature match.

**Complement substitution validity.** `sum_complements` constructs an equivalence via complementation. This is mathematically sound for `Finset (Fin n)` since complementation is an involution. No gap.

**`hterm` exponent arithmetic.** The claim `O Uᶜ Vᶜ = f U * f V / ((U ∪ V).card + 1)` expands to checking `x^(n - Uᶜ.card + n - Vᶜ.card) = x^(U.card + V.card)` after simplification. Since `Uᶜ.card = n - U.card`, we get `n - (n - U.card) + n - (n - V.card) = U.card + V.card`. But the numerator of `O` has `x^(n - S.card + n - T.card)` with `S = Uᶜ, T = Vᶜ`, giving `x^(U.card + V.card)`. Meanwhile `f U * f V = x^U.card / U.card! * x^V.card / V.card!`. The denominator of `O Uᶜ Vᶜ` includes `(n - (Uᶜ ∩ Vᶜ).card + 1)`; by De Morgan, `(Uᶜ ∩ Vᶜ) = (U ∪ V)ᶜ`, so its card is `n - (U ∪ V).card`, giving denominator factor `(U ∪ V).card + 1`. The factorial terms become `(n - Uᶜ.card)! = U.card!` and similarly for V. **This checks out—no gap.**

**Final CDF theorem is a direct rewrite.** `actualTwoExtraRows_minimum_CDF_meanSquares` simply combines the imported CDF theorem with the newly proved mean-squares identity. No independent mathematical content; no gap.

**Summary:** No actual mathematical gaps found in the proof bodies. The sole dependency risk is `twoExtraRowMinimumPolynomial_eq_overlapKernel`'s exact statement, which is properly flagged as external.
