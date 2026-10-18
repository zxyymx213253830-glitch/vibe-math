import JinWishartFormalization.CentralWishartDeterminantMoments
import JinWishartFormalization.GaussianSubmatrixLaw

/-! Actual principal-minor means for the central cone-polynomial route.
Codex proof bodies; Qoder route guidance. [需人工审查] Submatrix laws and moments.
-/
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal ComplexOrder
namespace JinWishart
noncomputable section

theorem complexWishart_principalMinor_norm_mean (n : ℕ) (S : Finset (Fin n)) :
    ∫⁻ W, ENNReal.ofReal ‖(W.submatrix (Subtype.val : S → Fin n)
      (Subtype.val : S → Fin n)).det‖ ∂complexWishart (m := n) (n := n) =
      ENNReal.ofReal (((Nat.factorial n : ℕ) : ℝ) /
        ((Nat.factorial (n - S.card) : ℕ) : ℝ)) := by
  classical
  let eS : Fin S.card ≃ S := Fintype.equivOfCardEq (by simp)
  let e : Fin S.card → Fin n := fun j => (eS j).val
  have he : Function.Injective e := Subtype.val_injective.comp eS.injective
  have hcard : S.card ≤ n := by
    simpa using Finset.card_le_card (Finset.subset_univ S)
  have h := complexWishart_determinant_norm_mean_of_le n S.card hcard
  rw [← complexWishart_principalSubmatrix_law (m := n) e he,
    lintegral_map (by fun_prop) (by fun_prop)] at h
  refine (lintegral_congr (fun W => ?_)).trans h
  have hm : (W.submatrix e e).det =
      (W.submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n)).det := by
    have hM : W.submatrix e e =
        (W.submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n)).submatrix eS eS := by
      ext i j
      rfl
    rw [hM, Matrix.det_submatrix_equiv_self]
  simp only [Function.comp_apply, hm]

theorem complex_norm_eq_re_of_nonneg (z : ℂ) (hz : 0 ≤ z) : ‖z‖ = z.re := by
  have h := Complex.nonneg_iff.mp hz
  have he : z = (z.re : ℂ) := by
    apply Complex.ext <;> simp [h.2]
  rw [he, Complex.norm_of_nonneg h.1, Complex.ofReal_re]

theorem complexWishart_principalMinor_re_mean (n : ℕ) (S : Finset (Fin n)) :
    ∫⁻ W, ENNReal.ofReal (W.submatrix (Subtype.val : S → Fin n)
      (Subtype.val : S → Fin n)).det.re ∂complexWishart (m := n) (n := n) =
      ENNReal.ofReal (((Nat.factorial n : ℕ) : ℝ) /
        ((Nat.factorial (n - S.card) : ℕ) : ℝ)) := by
  rw [← complexWishart_principalMinor_norm_mean n S]
  apply lintegral_congr_ae
  have hp : ∀ᵐ W ∂complexWishart (m := n) (n := n), W.PosSemidef :=
    (mem_ae_iff_prob_eq_one Matrix.posSemidef_is_closed.measurableSet).mpr
      complexWishart_measure_posSemidef
  filter_upwards [hp] with W hW
  congr 1
  exact (complex_norm_eq_re_of_nonneg _ (hW.submatrix _).det_nonneg).symm

end
end JinWishart

#print axioms JinWishart.complexWishart_principalMinor_norm_mean
#print axioms JinWishart.complex_norm_eq_re_of_nonneg
#print axioms JinWishart.complexWishart_principalMinor_re_mean
