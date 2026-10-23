# P4 Adversarial Review

## FiniteSpectrumFractionalOffset.lean

**1. Missing integrability/measure-theoretic conditions (stochastic gap).**
`logOneAddFractional` and `positiveModeOffsetError_fractional_bound` are pointwise real inequalities. The comment flags "Stochastic use of real powers," but no lemma in this file establishes measurability or integrability of `x ↦ x^α` for random spectra. This is not a flaw in the pointwise bound, but the stochastic application in the next file requires these properties separately. Treat as a dependency obligation, not a local gap.

**2. Division-by-zero risk in `a⁻¹` when minimum eigenvalue could be zero.**
`finiteSpectrumOffsetError_fractional_min_bound` assumes `hmin : ∀ i, 0 < x i → a ≤ x i` with `ha : 0 < a`. When `x i = 0`, the proof correctly handles this branch via `hz`. However, `a⁻¹` appears in the final bound. If all `x i = 0`, then `hmin` is vacuously true for any `a > 0`, so `a⁻¹` remains finite—no actual gap. But the bound becomes `(card ι) * α⁻¹ * (t⁻¹)^α * (a⁻¹)^α` which is nonzero despite the sum being exactly zero. This is logically valid but mathematically loose; not a correctness gap, only a tightness observation.

**3. API question (optional, not a mathematical gap).**
`Real.rpow_add_le_add_rpow` is invoked with specific arguments. The exact signature matters: if Mathlib's version requires strict positivity rather than nonnegativity of bases, the `hx : 0 ≤ x` hypothesis may be insufficient at the boundary `x = 0`. Verify that the imported lemma permits zero bases under `ha : 0 < α`.

## ActualSingularFractionalRates.lean

**4. Index coercion and rank identification fragility.**
The hypothesis `hi : i.val + 1 = min m r` combined with `he : i = i0` derived from `exists_actualCorrelated_smallest_positive_coordinate` uses `omega` after rewriting by `hr`. This identification is valid only if `exists_actualCorrelated_smallest_positive_coordinate` returns an index satisfying the same arithmetic relation. If that existential theorem produces a `Fin n` index with a different characterization (e.g., zero-indexed position vs. one-indexed rank), the `omega` step fails silently or proves a false equality. **This is a potential logical gap**: confirm that the returned `i0` satisfies `i0.val + 1 = min m r` under the theorem's own postconditions, not merely by coincidence of `hr`.

**5. AE filter composition assumes compatible null sets.**
`filter_upwards [hMin, actualCorrelatedRank_eq_generic_ae B M]` intersects two almost-everywhere sets. This is valid in complete measure spaces. However, `stdGaussian _` must be verified as a complete measure; otherwise the intersection of two conull sets need not be conull. Standard Gaussian measures on Polish spaces are complete, so this is likely satisfied, but it is an implicit assumption not stated in the theorem.

**6. Variance difference inequality direction.**
`variance_difference_le_mean_square` is applied as `|Var U - Var S| ≤ MSE + 2√(MSE)·√(Var S)`. Verify this lemma yields exactly this form. Some variance-difference bounds give `Var U - Var S ≤ ...` without absolute value, or require `U, S ∈ L²` with explicit centering. The proof shows `hUM : MemLp U 2 μ` and `hSM : MemLp S 2 μ`, which suffices, but confirm the lemma does not additionally assume mean-zero or identical means.

**7. Integrability obligation transfer.**
The mean-square bound invokes `actualCorrelatedMatrixLogDet_offset_mean_square` for `hErrI` integrability. This is a separate dependency. No local gap, but if that theorem's integrability conclusion is weaker (e.g., requires `t > 1` strictly rather than `t ≥ 1`), the `ht0 : 0 < t` deduction from `ht : 1 ≤ t` would not bridge it. Check endpoint inclusion.
