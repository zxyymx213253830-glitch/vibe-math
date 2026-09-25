import JinWishartFormalization.Theorem1FullRankDeterminantScaling

/-!
# Theorem 1: one noncentral eigenvalue and two rows

For `s=1`, `t=2`, and `L=1`, the paper's smallest-eigenvalue formula is a
single normalized Nuttall-Q tail. The denominator is kept as an explicit
nonvanishing hypothesis; proving that analytic fact for every positive
noncentrality is a separate task.
-/

namespace JinWishart

/-- The order and amplitude in the `s=1`, `t=2`, `L=1` specialization of
Theorem 1: equation (16) gives `p=2`, `q=1`. -/
noncomputable def theorem1TwoRowScalarQ (lambda x : ℝ) : ℂ :=
  nuttallQ 2 1 (Real.sqrt (2 * lambda)) (Real.sqrt (2 * x))

/-- Theorem 1's determinant candidate in the one-column, two-row noncentral
case is exactly one minus the normalized `Q_{2,1}` tail, whenever its
normalizing tail is nonzero. -/
theorem theorem1ScalarTwoRowsCandidate_eq_normalizedNuttallQ
    (lambda x : ℝ)
    (hden : nuttallQ 2 1 (Real.sqrt (2 * lambda)) 0 ≠ 0) :
    theorem1CdfCandidate 1 2 1 (by omega) (by omega)
      (fun _ : Fin 1 => lambda) x =
      1 - ‖theorem1TwoRowScalarQ lambda x‖ /
        ‖nuttallQ 2 1 (Real.sqrt (2 * lambda)) 0‖ := by
  have hdet : (theorem1FullRankQMatrix 1 2 (fun _ : Fin 1 => lambda) 0).det ≠ 0 := by
    simpa [theorem1FullRankQMatrix, theorem1QOrder] using hden
  rw [theorem1FullRankCandidate_eq_unscaledQ 1 2 (by omega)
    (fun _ : Fin 1 => lambda) x hdet]
  simp [theorem1FullRankQMatrix, theorem1QOrder, theorem1TwoRowScalarQ]

end JinWishart
