# P4 Adversarial Review: CandidateTraceLaplaceClosed.lean

## Actual Mathematical Gaps

**1. Division-by-zero risk in `field_simp` (critical)**

The final calculation uses `field_simp` to cancel `(mixedNoncentralMomentMatrix q p L lambda).det`. The proof establishes `hD : det ≠ 0` via contradiction using `hd : 0 < det`. However, the denominator term `(∏ j, Real.exp (lambda j)) * det` requires both factors nonzero. While `he` handles the exponential product, the logical flow from `hD` to the `field_simp` application is implicit—Lean's `field_simp` needs the exact nonzero lemma for the full denominator expression. If the automation doesn't assemble this from the conjuncts, the rewrite silently fails or produces a malformed goal.

**2. Scaling identity `mixedNoncentralMomentMatrix_det_div_scale` applied without domain check**

The theorem invokes `mixedNoncentralMomentMatrix_det_div_scale` inside `hfactors`, which substitutes `(fun b => lambda b / c)` into the moment matrix. This requires that dividing each `lambda j` by `c = 1 + s` preserves whatever structural conditions the scaling lemma demands (e.g., nonnegativity, strict monotonicity). The proof has `hc : 0 < c` and `hlp : ∀ j, 0 < lambda j`, so `lambda j / c > 0` holds, but **strict monotonicity of the scaled vector** is never explicitly verified. If `mixedNoncentralMomentMatrix_det_div_scale` requires `StrictMono (fun b => lambda b / c)`, this is a gap—dividing by a positive constant preserves ordering, but this step isn't shown.

**3. Exponential ratio simplification assumes `Finset.sum_div` applicability**

In `hex`, the rewrite chain uses `← Finset.sum_div` to convert `∑ (lambda j / c)` into `(∑ lambda j) / c`. This is valid only if `c` is independent of the summation index, which it is—but `Finset.sum_div` in Mathlib typically requires the divisor to be a unit or lives in a field context. Over `ℝ` with `hc : c ≠ 0` this should close, yet the proof buries this inside `field_simp; ring` without explicitly discharging the side condition that `c` is invertible in the relevant algebraic structure.

**4. Implicit Fubini/measurability discharge**

The header flags `[需人工审查] Fubini, normalization and model mapping`. The integral over `Fin (p+L) → ℝ` against `mixedCandidateEnsemble` is manipulated via `mixedCandidateEnsemble_trace_laplace_scaled_det` without any stated measurability or integrability hypothesis on the exponential kernel `Real.exp (-s * ∑ i, z i)`. For `hs : 0 ≤ s`, the integrand is bounded above by 1 only when `∑ z_i ≥ 0`, which depends on the support of the candidate ensemble. If the measure's support isn't confined to nonneg reals (not stated in assumptions), integrability is an open gap.

## Optional API/Signature Questions

- `weightedMixedColumnFactor_prod`: The RHS splits the product over `Fin p ⊕ Fin L` into separate products. This requires `Fintype.prod_sum_type` to apply to `weightedMixedColumnFactor`'s specific definition—a semantic match question, not a math gap.
- `mixedEnsemble_momentMatrix_det`: Uses `volume.restrict (Ioi 0)` as the base measure. Whether this matches the imported `mixedEnsemble_momentMatrix_eq`'s expected measure argument is an API-level concern.
