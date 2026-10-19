# P4 Audit: `centralMinimumPDFCore_sharp_coefficient_limit`

## 1. Standard 3-Axiom Compliance (kernelPASS)
- `#print axioms` on both files confirms dependency only on standard Mathlib analytic infrastructure (`AnalyticAt`, `iteratedDeriv`, `Tendsto`). No exotic axioms introduced. **PASS.**

## 2. Taylor Lemma Application
- `analytic_ratio_limit_of_vanishing` correctly requires no positivity/log assumptions. 
- Instantiation with `f := centralMinimumPDFCore d n` and `k := d` is type-correct.
- Vanishing of lower derivatives `hz` properly lifts from CDF order `d+1` via `← he` and `← iteratedDeriv_succ'`. Index shift `i < d → i+1 ≤ d` is handled by `omega`. **PASS.**

## 3. Factorial/Index Inspection
- Target coefficient: `(d+1) * a`.
- Proof derives `iteratedDeriv d h 0 / d! = (d+1)! * a / d!`.
- Reduction uses `Nat.factorial_succ` to rewrite `(d+1)! = (d+1) * d!`, then `field_simp` cancels `d! ≠ 0`. Arithmetic is exact. **PASS.**

## 4. One-Sided Filter & Canonical RN PDF
- Limit uses `𝓝[>] 0` (`nhdsWithin (Set.Ioi 0)`), correctly restricting to the right edge.
- `hlim` construction filters through `self_mem_nhdsWithin` ensuring `0 < x` before division by `x^k`.
- Result applies strictly to the analytic core `h = G'`, not a piecewise CDF derivative or joint/noncentral density. **PASS.**

## 5. Edge Case `d = 0`
- When `d = 0`, `hz : ∀ i < 0, ...` is vacuously true. No lower derivatives to check.
- Limit becomes `h(x)/x^0 → 1 * a`, yielding density `a` at `0⁺`.
- Boundary PDF value being 0 almost everywhere is irrelevant; this captures the pointwise analytic core limit. **PASS.**

## 6. Mandatory Human Review Items (P4 Flags)
> **WARNING:** Formalization passes kernel checks, but human measure/model review is REQUIRED for the following semantic gaps:

1. **Measure Interpretation**: The Lean definition of `centralMinimumPDFCore` as the Radon-Nikodym derivative of the actual minimum measure must be validated against the intended probabilistic model. Kernel accepts the calculus; it does not verify the measure-theoretic grounding.
2. **Hard Edge Convention**: Confirm that `centralMinimumFiniteHardEdgeCoefficient` matches the domain-specific definition of the "actual general CENTRAL minimum" factorial functional coefficient `a`, rather than a simplified classical constant.
3. **Analytic Continuation vs. Piecewise CDF**: Ensure `G` (`centralMinimumCDFContinuation`) is universally accepted in your framework as the *separate analytic continuation* rather than the raw piecewise CDF. The derivative equivalence `he` relies on this distinction.
4. **AE vs. Pointwise**: The theorem proves pointwise convergence of the analytic core ratio. Verify this aligns with the intended use case, as canonical RN PDFs are typically defined only up to AE equivalence classes.

**Summary**: Lean4 formalization is structurally sound and axiomatically standard. All derivative indices, factorial cancellations, and filter restrictions are correct. Release to human reviewers for measure-theoretic and modeling sign-off.
