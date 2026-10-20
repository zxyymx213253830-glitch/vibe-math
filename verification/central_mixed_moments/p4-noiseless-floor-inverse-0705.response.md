# Adversarial Review: Issues Only

## CorrelatedNoiselessSpectralFloor.lean

**1. Potential `simpa` failure in `exists_noiseless_right_inverse` (surjectivity step)**
The `simpa only [Module.finrank_pi, Fintype.card_fin] using hs` relies on `LinearMap.range a` reducing definitionally to a `Fin m → ℂ` module whose `finrank` is computable as `m`. If the `domRestrict` range does not unfold to exactly `Pi (Fin m) ℂ`, this `simpa` will silently fail or require additional lemmas not in scope. This is a hidden definitional-dependency risk.

**2. Matrix–linear-map bridge simp set fragility**
In both `hb` and `hm` goals inside `exists_noiseless_right_inverse`, the `simpa only [...]` chains use `LinearMap.toMatrix'_comp`, `← Matrix.toLin'_apply'`, `LinearMap.toMatrix'_toLin'`, etc. These rewrites assume exact syntactic alignment between `B.mulVecLin`, `M.mulVecLin`, `LinearMap.toMatrix'`, and their composition/identity lemmas. Any Mathlib refactor of these simp lemmas (or a missing `@[simp]` tag upstream) breaks the chain. No fallback `rw` sequence is provided.

**3. Operator norm squared vs. `noiselessRightInverseControl` gap**
`noiselessRightInverseControl` is defined as `max 1 (‖...‖^2)`. In `rowGram_minimum_lower_of_right_inverse`, the bound derived is `1 / ‖Cᴴ‖_op^2 ≤ gramSmallestValue`. The final step uses `le_max_right _ _` to say `‖Cᴴ‖_op^2 ≤ noiselessRightInverseControl C`. This is correct, but note that when `‖Cᴴ‖_op^2 < 1`, the control equals 1, making the floor `1/1 = 1`, which is **strictly stronger** than what the operator norm alone gives (`1/‖Cᴴ‖^2 > 1`). This is logically sound but means the `max 1` is doing real work that is never documented; a reader might mistakenly think the bound is always `1/‖Cᴴ‖^2`.

**4. `gramSmallestValue_nonneg` used but never proved here**
`hn := gramSmallestValue_nonneg Xᴴ hm` is imported from elsewhere. If that upstream lemma has a side condition (e.g., `0 < m`) that differs from the local `hm`, it would mismatch. Scope is limited to imports being separately verified, but the local proof depends on it for the `nlinarith` closure.

**5. Dimension/rank assumption scope**
The hypothesis `hs : finrank ... = m` implicitly requires `m ≤ n` and `m ≤ p` (since the domain is `ker B.mulVecLin ⊆ Fin n → ℂ` and the codomain is `Fin m → ℂ`). This is never stated explicitly. If `m > n`, the kernel restriction cannot have rank `m`, making `hs` vacuously unsatisfiable rather than producing a clean "impossible" goal. Not a bug, but a hidden dimensional constraint.

---

## CorrelatedNoiselessInverseMoments.lean

**6. `Measurable.of_eval_matrix` usage**
The proof of `measurable_actualCorrelatedRowMinimum` applies `Measurable.of_eval_matrix` then discharges entry-wise measurability with `fun_prop`. This assumes `complexSampleMatrix z * B + M` has entries that are measurable functions of `z : ComplexSample m p`. Since `ComplexSample` carries the product measurable structure and matrix multiplication is polynomial in entries, this should hold, but `fun_prop` must resolve the composition through `Matrix.mul_apply` (a finite sum of products). If `fun_prop` lacks the relevant instances for `ℂ`-valued sums/products in the ambient σ-algebra, it silently fails.

**7. `integrable_const` domination requires `δ⁻¹ ^ pwr` finite**
`δ > 0` ensures `δ⁻¹` is finite, so `(δ⁻¹) ^ pwr` is a finite constant for `pwr ≥ 0`. Correct. However, the statement uses `Real.rpow` (`^ pwr` for `pwr : ℝ`), and `integrable_const` needs the constant to be a valid `ENNReal`-integrable value. For `pwr = 0` this gives `1`, fine. No issue, but the `hpwr : 0 ≤ pwr` guard is essential and correctly present.

**8. `ae_of_all` with universal quantification over `z`**
The proof uses `ae_of_all` to show the pointwise bound holds **everywhere**, not just a.e. This is valid because `correlated_rowGram_uniform_floor` provides a deterministic `∀ Z` bound. No measure-theoretic subtlety arises. Correct.

**9. `abs_of_nonneg` + `Real.rpow_nonneg` chain**
The step `rw [abs_of_nonneg (Real.rpow_nonneg (inv_nonneg.mpr hpos.le) pwr)]` requires `hpos.le : 0 ≤ gramSmallestValue ...`. But `hpos` is `0 < gramSmallestValue ...` obtained from `hδ.trans_le hz` where `hδ : 0 < δ`. This is fine; strict positivity implies nonnegativity. No gap.

**10. No inverse-moment existence claim for singular factors**
The docstring explicitly states "This is NOT the inverse minimum criterion for every singular factor." The theorem only covers the row-Gram minimum under the surjectivity condition `hs`. No scope mismatch, but worth noting that `hs` is the sole gatekeeper: if `hs` fails, no bound is produced, and the module makes no attempt to handle that case.

---

## Cross-module / meta issues

**11. `[需人工审查]` tags are placeholders, not proofs**
Both files carry `[需人工审查]` for operator/spectral correspondence and measurability/model correspondence. These are explicit markers that the formalization does **not** close the loop between the mathematical model (CN1 source with two standard real coordinates divided by √2) and the Lean statements. The theorems as stated are internally consistent but their applicability to the intended physical/statistical model is unverified within these modules.

**12. Zero-dimension intentionality**
Per instructions, zero dimensions are intentional. The `hm : 0 < m` guard prevents degenerate `Fin 0` edge cases in `gramSmallestValue`. If `m = 0` were permitted, `1/noiselessRightInverseControl C ≤ gramSmallestValue Xᴴ hm` would need separate handling. The current scope excludes this by fiat.

**13. Import dependency, not re-proved**
`exists_gram_minimum_unit_vector`, `gramSmallestValue_nonneg`, `measurable_gramSmallestValue`, and the entire `ComplexSample`/`stdGaussian` infrastructure are imported. Per instructions, these are separately checked. This review does not audit them, but notes that the correctness of `rowGram_minimum_lower_of_right_inverse` and `actualCorrelatedRow_inverseMoment_integrable_of_noiseless_surjective` is conditional on those imports matching their expected signatures and side conditions.

---

**Summary of actionable concerns:** Items 1, 2, and 6 represent potential compilation/maintenance fragility points where `simpa`/`fun_prop` depend on exact definitional unfolding or typeclass resolution that may drift. Item 5 is a documentation gap regarding implicit dimensional constraints. Items 11–13 are acknowledged scope limitations, not bugs.
