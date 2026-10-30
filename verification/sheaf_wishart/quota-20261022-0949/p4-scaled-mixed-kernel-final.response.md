# P4 Adversarial Review: ScaledMixedKernelMoments.lean

## 1. Missing Integrability Hypotheses (Actual Gap)

`integral_const_mul` and `integral_comp_mul_left_Ioi` require the integrand to be integrable (or at least measurable with well-defined extended integral). Theorem `scalarSeriesKernel_scaledMoment` applies these rewrites without establishing that `t^(q+k) * Real.exp(-(c*t)) * scalarSeriesKernel q lambda t` is integrable on `Ioi 0`. The proof assumes the substitution is valid and then invokes `scalarSeriesKernel_weightedMoment` at the end, but the intermediate rewrite steps via `rw [hf, integral_const_mul, ...]` are only justified if the resulting integrals exist. This should either add an `Integrable` hypothesis or prove integrability from `hc : 0 < c` and the exponential decay.

Similarly, `integral_natPower_exp_neg_scaled` uses `integral_const_mul` and `integral_comp_mul_left_Ioi` without explicit integrability premises.

## 2. Potential Signature Mismatch on `integral_comp_mul_left_Ioi`

The theorem calls:
```
integral_comp_mul_left_Ioi (fun t => t^k * Real.exp (-t)) 0 hc
```
This requires the lemma to accept a function `ℝ → ℝ`, a lower bound, and a positivity proof for the scaling constant. If the actual signature in Mathlib (or the imported file) requires additional measurability conditions or uses a different formulation (e.g., `AEStronglyMeasurable`), this would fail. This is an **API question**, not a mathematical gap, but it blocks compilation if the signature doesn't match exactly.

## 3. Division by Zero Risk in `scalarSeriesKernel_scale`

The proof uses `div_pow` which expands `(lambda/c)^m` to `lambda^m / c^m`. While `hc : 0 < c` ensures `c ≠ 0`, the `field_simp` step relies on `hn : c^m ≠ 0`. This is correctly derived. No issue here—just noting it's handled.

## 4. Unstated Domain Constraint on `scalarSeriesKernel`

The scaling identity `scalarSeriesKernel q (lambda/c) (c*t) = scalarSeriesKernel q lambda t` is stated for all `t : ℝ`, but the kernel may only have its intended series representation converge for `t ≥ 0` (given the context of Laplace-type integrals over `Ioi 0`). The theorem statement imposes no constraint on `t`. If the underlying definition involves a `tsum` that only converges for non-negative arguments, this identity could be false or meaningless for `t < 0`. The subsequent integral theorems restrict to `Ioi 0`, but the pointwise identity does not.

## 5. Coercion Consistency

`(k.factorial : ℝ)` and casts like `c^(k+1)` mixing `ℕ` exponents with `ℝ` bases are standard but rely on correct `Nat.cast` instances. No mathematical gap, but if `poissonFactorialMomentPolynomial` expects `ℕ` vs `ℝ` arguments differently than presented, type mismatch occurs. **API-level concern only.**

## Summary

**Actual mathematical gaps:** Missing integrability justifications for integral substitution lemmas (items 1–2); unconstrained domain for the pointwise scaling identity (item 4).

**API questions (not logical errors):** Exact signatures of `integral_comp_mul_left_Ioi`, `integral_const_mul`, and argument types for `poissonFactorialMomentPolynomial`.
