## P4 Issues-Only Review

**Scope supplied:** 12 statements across two new files (4 + 8), plus 79 lines of support context. All reportedly pass local Lean axiom checks. I do not independently compile.

### Concrete Issues Found

**1. Complex vs Real Linearity — `exists_complex_nonzero_frame` (File 1, calc block)**

The step `U a = ‖a‖ • U (‖a‖⁻¹ • a)` invokes `(complexFrameToReal U).map_smul _ _`. This is **correct** but fragile: `U` is `≃ₗᵢ[ℂ]`, yet the scalar `‖a‖ : ℝ` requires real-linearity. The explicit cast to `complexFrameToReal` discharges this, but the proof omits type ascription on `‖a‖`, relying on coercion `ℝ → ℂ`. Not a bug, but a maintenance risk if Mathlib's coercion priorities shift.

**2. sqrt(2) Convention — Consistency Check**

File 1 has no `√2` factors (frame-level). File 2 introduces `(Real.sqrt 2)⁻¹` in `complexSampleMatrix_column_coordinates` to match the support file's convention where `complexColumnCoordinates_join_first` divides by `√2`. **Consistent.** The support file explicitly states "no sqrt(2) in the isometry; the actual complex sample has the additional variance factor." No issue.

**3. Coordinate Curry Direction — `matrixColumnIndexEquiv` (File 2)**

The equiv maps `((Fin m × Fin n) × Fin 2) ≃ (Σ _ : Fin n, Fin m × Fin 2)`, currying columns-first. Application theorem `complexSampleByColumns_apply` confirms `z j (i, k) = z ((i, j), k)`. **Direction is correct** for column-wise unitary action.

**4. Full Matrix Law vs Scalar Energy — `complexGaussianMatrixLaw_unitary_invariant` (File 2)**

This proves the **full central matrix law** pushforward equality, not merely trace/energy. Uses `Measure.map_map` composition with `encodedComplexMatrixFrame_gaussianLaw`. **Correct scope.** No scalar reduction leak.

**5. All Columns — `unitaryActColumns` (File 2)**

Defined as `fun i j => U (complexMatrixColumn A j) i`, applying `U` uniformly per-column. The Gram invariance theorem quantifies over all `j k`. **All columns covered.**

**6. No Global Choice Claimed**

Both files' docstrings explicitly state pointwise existential frames only. No measurable selector is constructed. **Within stated scope.**

### Human-Review Limit

I verified logical structure, type-class consistency, and convention alignment against the support file. I did **not** check Mathlib API stability for `Orthonormal.exists_orthonormalBasis_extension_of_card_eq` or `LinearIsometryEquiv.piLpCurry` signatures. Compilation trust is delegated to your local check.

**Verdict:** No blocking issues. One minor robustness note (item 1). Scope and conventions are respected.
