import JinWishartFormalization.Theorem1FullRankDeterminantScaling

/-!
# Theorem 1: rank-one noncentrality and one Wishart eigenvalue

For `s=L=1` and arbitrary `t≥1`, equation (16) has a single active
Nuttall-Q column with indices `(p,q)=(t,t-1)`. Factoring the common row
prefactor reduces the determinant ratio to a scalar normalized tail ratio.
The normalizing Nuttall-Q tail is assumed nonzero explicitly.
-/

namespace JinWishart

/-- The order pair in Theorem 1's single-column specialization at arbitrary
row count `t`: `p=t`, `q=t-1`. -/
noncomputable def theorem1OneColumnNuttallQ (t : ℕ) (lambda x : ℝ) : ℂ :=
  nuttallQ t (t - 1) (Real.sqrt (2 * lambda)) (Real.sqrt (2 * x))

/-- For any `t≥1`, the `s=L=1` Theorem 1 determinant candidate is exactly
one minus the normalized `Q_{t,t-1}` tail. The denominator condition is
explicit, as required to interpret the ratio. -/
theorem theorem1OneColumnCandidate_eq_normalizedNuttallQ
    (t : ℕ) (ht : 1 ≤ t) (lambda x : ℝ)
    (hden : nuttallQ t (t - 1) (Real.sqrt (2 * lambda)) 0 ≠ 0) :
    theorem1CdfCandidate 1 t 1 ht (by omega) (fun _ : Fin 1 => lambda) x =
      1 - ‖theorem1OneColumnNuttallQ t lambda x‖ /
        ‖nuttallQ t (t - 1) (Real.sqrt (2 * lambda)) 0‖ := by
  have horder : ∀ i : Fin 1, theorem1QOrder 1 t i = t := by
    intro i
    fin_cases i
    simp [theorem1QOrder]
    omega
  have hdet : (theorem1FullRankQMatrix 1 t (fun _ : Fin 1 => lambda) 0).det ≠ 0 := by
    simpa [theorem1FullRankQMatrix, horder] using hden
  rw [theorem1FullRankCandidate_eq_unscaledQ 1 t ht
    (fun _ : Fin 1 => lambda) x hdet]
  simp [theorem1FullRankQMatrix, horder, theorem1OneColumnNuttallQ]

end JinWishart
