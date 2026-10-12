import JinWishartFormalization.TwoRowActualNormalizedDensity

/-! Codex spectral threshold bridge. No density assumption.
[需人工审查] Identification of this exact matrix event with paper conventions. -/

open Matrix Unitary
open scoped ComplexOrder

namespace JinWishart
noncomputable section

theorem hermitian_twoRow_shift_posDef_iff (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A.IsHermitian) (x : ℝ) :
    (A - (x : ℂ) • 1).PosDef ↔ ∀ i, x < hA.eigenvalues i := by
  have he :
      conjStarAlgAut ℂ _ hA.eigenvectorUnitary
          (diagonal (fun i => (hA.eigenvalues i : ℂ) - (x : ℂ))) =
        A - (x : ℂ) • 1 := by
    calc
      _ = conjStarAlgAut ℂ _ hA.eigenvectorUnitary
          (diagonal (fun i => (hA.eigenvalues i : ℂ)) - (x : ℂ) • 1) := by
            rw [smul_one_eq_diagonal, diagonal_sub]
      _ = A - (x : ℂ) • 1 := by
            rw [map_sub, map_smul, map_one]
            congr 1
            simpa only [Function.comp_def, RCLike.ofReal_eq_complex_ofReal]
              using hA.spectral_theorem.symm
  rw [← he, conjStarAlgAut_apply, isUnit_coe.posDef_star_right_conjugate_iff,
    posDef_diagonal_iff]
  simp only [← Complex.ofReal_sub, Complex.zero_lt_real, sub_pos]

theorem hermitian_twoRow_shift_posDef_iff_smallest
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.IsHermitian) (x : ℝ) :
    (A - (x : ℂ) • 1).PosDef ↔ x < hA.eigenvalues₀ 1 := by
  rw [hermitian_twoRow_shift_posDef_iff A hA x]
  have hforall : (∀ i, x < hA.eigenvalues i) ↔ ∀ i, x < hA.eigenvalues₀ i := by
    let e : Fin (Fintype.card (Fin 2)) ≃ Fin 2 :=
      Fintype.equivOfCardEq (Fintype.card_fin _)
    change (∀ i, x < hA.eigenvalues₀ (e.symm i)) ↔ ∀ i, x < hA.eigenvalues₀ i
    constructor
    · intro h i
      simpa using h (e i)
    · intro h i
      exact h (e.symm i)
  rw [hforall]
  constructor
  · intro h
    exact h 1
  · intro h i
    have hi : i ≤ 1 := by
      change i.val ≤ 1
      have hb := i.isLt
      norm_num at hb
      omega
    exact lt_of_lt_of_le h (hA.eigenvalues₀_antitone hi)

end
end JinWishart

#print axioms JinWishart.hermitian_twoRow_shift_posDef_iff
#print axioms JinWishart.hermitian_twoRow_shift_posDef_iff_smallest
