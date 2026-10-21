# P4 Adversarial Review: ExpectedLogDetDerivative.lean

## 1. Dominated Convergence Bound is Mathematically Wrong (Critical Gap)

In `integral_log_one_add_mul_hasDerivAt`, the domination proof (bullet 4) establishes:

```
|f a / (1 + x * f a)| ≤ f a
```

by proving `1 ≤ 1 + x * f a` via `nlinarith`. This bound holds pointwise for each fixed `x > 0`. However, `hasDerivAt_integral_of_dominated_loc_of_deriv_le` requires a **single integrable dominating function valid uniformly in a neighborhood of `r`**. The proof supplies `bound := f`, which is independent of `x`, but the inequality `|f/(1+x*f)| ≤ f` degrades as `x → 0⁺`. For the theorem statement at hand (derivative at `r > 0`), this is salvageable because `Ioi_mem_nhds hr` restricts to a neighborhood bounded away from 0, so `1/(1+x*f) ≤ 1` remains valid. **However**, the formal argument never explicitly uses that `x` stays in a set where `x ≥ ε > 0` to tighten the bound—it just asserts the pointwise inequality for all `x ∈ Ioi 0`, which is technically sufficient but only because `hr : 0 < r` and the filter is `Ioi_mem_nhds hr`. This is correct but fragile; no actual gap here upon close reading, though the exposition obscures why the neighborhood matters.

**Verdict**: Not a gap, but the proof structure is misleading—the domination `|f'| ≤ f` is only useful because the neighborhood excludes 0, which is guaranteed by `hr`.

## 2. Missing Integrability of the Derivative Expression (Actual Gap)

The theorem asserts `Integrable (fun a => f a / (1 + r * f a)) μ` as part of the conclusion but then immediately uses `hasDerivAt_integral_of_dominated_loc_of_deriv_le`, which **requires** the derivative function to be integrable as a hypothesis (or derives it from domination). Bullet 5 supplies `hf : Integrable f μ` as the domination witness. But the API call pattern shown does not explicitly discharge the integrability-of-derivative side condition beyond domination. If `hasDerivAt_integral_of_dominated_loc_of_deriv_le` demands a separate proof that `F' r` is integrable (not merely dominated), this is an omitted obligation. Given the stated signature, domination by an integrable function should suffice, so this may be an API question rather than a true gap—**but** if the Mathlib lemma requires `Integrable (F' r) μ` as a distinct premise, it is missing.

**Verdict**: Potential gap depending on exact API signature; likely resolvable from domination + measurability already present.

## 3. Eigenvalue Index Type Mismatch (Minor API Question)

`actualCorrelated_expected_logdet_hasDerivAt` indexes eigenvalues by `Fin (Fintype.card (Fin n))`, which is definitionally `Fin n` but not syntactically identical. The sum `∑ i : Fin n` in the conclusion implicitly coerces. This is standard and not a mathematical gap.

## 4. Exchange of Sum and Integral (No Gap)

The final rewrite uses `integral_finsetSum` with a finiteness proof. Since the index type is finite, Fubini/Tonelli conditions are trivially satisfied. Correct.

## Summary

- **One genuine concern**: Whether integrability of the pointwise derivative at `r` is fully discharged or relies on an implicit API behavior of `hasDerivAt_integral_of_dominated_loc_of_deriv_le`.
- **No fatal mathematical errors** in the differentiation logic itself.
- All other steps (domination, spectral decomposition, sum-integral exchange) are sound given the stated hypotheses.
