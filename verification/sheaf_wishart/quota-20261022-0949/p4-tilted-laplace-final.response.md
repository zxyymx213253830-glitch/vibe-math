# P4 Adversarial Review

## `LocalDualMGFLawUniqueness.lean`

**1. Missing `CompleteSpace E` on the imported uniqueness lemma (semantic gap).**
The theorem assumes `[CompleteSpace E]` and calls `map_eq_of_mgf_eventuallyEq_zero`. This dependency is treated as separately checked, but the characteristic-function inversion principle (`Measure.ext_of_charFunDual`) for infinite-dimensional Banach spaces requires tightness/Prokhorov-type arguments that depend on completeness and second countability. If the imported lemma's signature omits `CompleteSpace E` or `SecondCountableTopology E`, this is a hard mathematical gap, not an API question. The explicit assumptions here are sufficient; verify the imported signature matches.

**2. No positivity or probability assumption on μ, ν.**
The measures are only `[IsFiniteMeasure μ] [IsFiniteMeasure ν]`. Characteristic function uniqueness holds for finite signed measures, so this is mathematically sound. Not a gap.

## `DominatedLocalLaplaceUniqueness.lean`

**3. Domain mismatch in `hLaplace`: actual mathematical gap.**
The hypothesis `hLaplace` quantifies over `L : E →L[ℝ] ℝ` with `‖L‖ < 1`. Inside the proof, it is applied to `t • L` where `‖t • L‖ < 1`. However, `hLaplace` is stated for **all** continuous linear maps of norm < 1, while `t • L` ranges over scalar multiples of a **fixed** `L`. This is fine: for each fixed `L`, the map `t • L` is indeed a continuous linear map, and when `‖t • L‖ < 1` it falls within the quantification of `hLaplace`. **Not a gap on reflection**, but the universal quantifier in `hLaplace` is stronger than needed (only rays through origin are used). Mathematically valid as stated.

**4. The domination condition `‖x‖ ≤ f x` a.e. does not imply `f ≥ 0` everywhere.**
The integrability proof uses `Real.exp (-f x + L x)`. If `f x < 0` on a null set, `Real.exp (-f x)` could be large there, but `withDensity` uses `ENNReal.ofReal (Real.exp (-f x))` which is defined pointwise. Since `hdom` is only almost-everywhere, the density `w` might not dominate `‖x‖` on the exceptional null set. However, `withDensity` and all integral identities respect a.e.-equality, so the null set is irrelevant. **Not a gap.**

**5. `withDensity_inv_same` requires the density to recover the original measure (potential gap).**
The final step rewrites `μ = (μ.withDensity w).withDensity w⁻¹` using `withDensity_inv_same`. This requires `w x ≠ 0` and `w x ≠ ⊤` for all `x`, which are proved (`hnz`, `hnt`). However, `withDensity_inv_same` typically requires the inverse density to be applied to the **tilted** measure to recover `μ`. The proof shows `μ.withDensity w = ν.withDensity w` (as `he`), then untilds both sides. This is logically correct **if** `withDensity_inv_same` states `(ρ.withDensity w).withDensity (fun x ↦ (w x)⁻¹) = ρ` under the nonvanishing conditions. Verify this exact signature. If the lemma instead requires integrability of the inverse density against the tilted measure, that condition is not discharged here. **API-level question that matters semantically.**

**6. No assumption that `f` is integrable or that `exp(-f)` defines a finite tilted measure a priori.**
The finiteness of `μ.withDensity w` is *proved* internally via `anchored_exp_integrable` at `L = 0`, which gives `∫ exp(-f x) dμ < ∞` using `‖x‖ ≤ f x` implying `exp(-f x) ≤ exp(-‖x‖) ≤ 1`. This is correct. **Not a gap.**

**7. Measurability of `f` is assumed but `hf : Measurable f` combined with `hdom` (a.e. bound) suffices.**
No issue.

## Summary of actual problems

- **`DominatedLocalLaplaceUniqueness`**: Verify the exact signature of `withDensity_inv_same`. If it requires integrability of `w⁻¹` against `μ.withDensity w` rather than just pointwise nonvanishing, that hypothesis is missing. This is the only potential mathematical gap.
- **`LocalDualMGFLawUniqueness`**: Confirm `map_eq_of_mgf_eventuallyEq_zero` accepts the generality of `[NormedAddCommGroup E] [CompleteSpace E]` without requiring local convexity or separability beyond `SecondCountableTopology`.
