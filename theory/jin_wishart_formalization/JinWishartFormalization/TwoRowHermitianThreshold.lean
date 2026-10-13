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

theorem hermitian_twoRow_det_re (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A.IsHermitian) :
    A.det.re = (A 0 0).re * (A 1 1).re - (A 0 1).re ^ 2 - (A 0 1).im ^ 2 := by
  have h0 : (A 0 0).im = 0 := by
    have h := congrArg Complex.im (hA.apply 0 0)
    simp only [RCLike.star_def, Complex.conj_im] at h
    linarith
  have h1 : (A 1 1).im = 0 := by
    have h := congrArg Complex.im (hA.apply 1 1)
    simp only [RCLike.star_def, Complex.conj_im] at h
    linarith
  rw [Matrix.det_fin_two, ← hA.apply 1 0]
  simp [Complex.mul_re, RCLike.star_def, h0, h1]
  ring

/-- The 2x2 Hermitian positive-definiteness criterion, proved using the already
available spectral trace and determinant formulas rather than assumed spectrum. -/
theorem hermitian_twoRow_posDef_iff (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A.IsHermitian) :
    A.PosDef ↔ 0 < (A 0 0).re ∧ 0 < A.det.re := by
  constructor
  · intro hp
    have hd : (0 : ℂ) < A 0 0 := hp.diag_pos
    exact ⟨(Complex.pos_iff.mp hd).1, (Complex.pos_iff.mp hp.det_pos).1⟩
  · intro h
    have h11 : 0 < (A 1 1).re := by
      have ht := hermitian_twoRow_det_re A hA
      have hm : 0 < (A 0 0).re * (A 1 1).re := by
        nlinarith [sq_nonneg (A 0 1).re, sq_nonneg (A 0 1).im]
      exact (mul_pos_iff_of_pos_left h.1).mp hm
    have htrace : (A 0 0).re + (A 1 1).re =
        hA.eigenvalues 0 + hA.eigenvalues 1 := by
      have ht := congrArg Complex.re hA.trace_eq_sum_eigenvalues
      simpa [Matrix.trace, Fin.sum_univ_two, RCLike.ofReal_eq_complex_ofReal] using ht
    have hdet : A.det.re = hA.eigenvalues 0 * hA.eigenvalues 1 := by
      have ht := congrArg Complex.re hA.det_eq_prod_eigenvalues
      simpa [Fin.prod_univ_two, RCLike.ofReal_eq_complex_ofReal] using ht
    have hsum : 0 < hA.eigenvalues 0 + hA.eigenvalues 1 := by
      rw [← htrace]
      exact add_pos h.1 h11
    have hprod : 0 < hA.eigenvalues 0 * hA.eigenvalues 1 := by
      rw [← hdet]
      exact h.2
    apply hA.posDef_iff_eigenvalues_pos.mpr
    intro i
    fin_cases i
    · change 0 < hA.eigenvalues 0
      by_contra hn
      have hb : 0 < hA.eigenvalues 1 := by linarith only [hsum, le_of_not_gt hn]
      exact not_le_of_gt hprod
        (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hb.le)
    · change 0 < hA.eigenvalues 1
      by_contra hn
      have hb : 0 < hA.eigenvalues 0 := by linarith only [hsum, le_of_not_gt hn]
      exact not_le_of_gt hprod
        (mul_nonpos_of_nonneg_of_nonpos hb.le (le_of_not_gt hn))

end
end JinWishart

#print axioms JinWishart.hermitian_twoRow_shift_posDef_iff
#print axioms JinWishart.hermitian_twoRow_shift_posDef_iff_smallest
#print axioms JinWishart.hermitian_twoRow_det_re
#print axioms JinWishart.hermitian_twoRow_posDef_iff
