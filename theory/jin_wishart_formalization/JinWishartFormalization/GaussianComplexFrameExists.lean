import JinWishartFormalization.GaussianComplexColumnFrame

/-!
# A fixed complex frame for a nonzero Gaussian column

Codex proofs using the locked orthonormal-basis extension theorem. These are
pointwise existential frames only. No joint measurable choice of frame is
asserted or needed by the planned fixed-fiber proof of a Gram-valued law.
[需人工审查] Future use of these frames inside fixed-fiber measure proofs and
the distinction between complex-unitary and merely real rotations.
-/

open MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

def complexFirstBasisVector (m : ℕ) : EuclideanSpace ℂ (Fin (m + 1)) :=
  EuclideanSpace.single 0 1

theorem exists_complex_unit_frame (m : ℕ) (a : EuclideanSpace ℂ (Fin (m + 1)))
    (ha : ‖a‖ = 1) :
    ∃ U : EuclideanSpace ℂ (Fin (m + 1)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (m + 1)),
      U a = complexFirstBasisVector m := by
  classical
  have horth : Orthonormal ℂ
      (({0} : Set (Fin (m + 1))).domRestrict
        (fun _ : Fin (m + 1) => a)) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hi : (i : Fin (m + 1)) = 0 := Set.mem_singleton_iff.mp i.property
    have hj : (j : Fin (m + 1)) = 0 := Set.mem_singleton_iff.mp j.property
    have hij : i = j := Subtype.ext (hi.trans hj.symm)
    subst j
    simp [inner_self_eq_norm_sq_to_K, ha]
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (by simp : Module.finrank ℂ (EuclideanSpace ℂ (Fin (m + 1))) =
      Fintype.card (Fin (m + 1))) horth
  refine ⟨b.repr, ?_⟩
  have hb0 : b 0 = a := hb 0 (by simp)
  rw [← hb0]
  exact b.repr_self 0

theorem exists_complex_nonzero_frame (m : ℕ) (a : EuclideanSpace ℂ (Fin (m + 1)))
    (ha : a ≠ 0) :
    ∃ U : EuclideanSpace ℂ (Fin (m + 1)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (m + 1)),
      U a = ‖a‖ • complexFirstBasisVector m := by
  have hpos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hnorm : ‖‖a‖⁻¹ • a‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos),
      inv_mul_cancel₀ (ne_of_gt hpos)]
  obtain ⟨U, hU⟩ := exists_complex_unit_frame m (‖a‖⁻¹ • a) hnorm
  refine ⟨U, ?_⟩
  calc
    U a = U (‖a‖ • (‖a‖⁻¹ • a)) := by
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hpos), one_smul]
    _ = ‖a‖ • U (‖a‖⁻¹ • a) := (complexFrameToReal U).map_smul _ _
    _ = _ := by rw [hU]

/-- A fixed complex frame preserves the actual real standard Gaussian law. -/
theorem exists_complex_nonzero_gaussian_frame (m : ℕ)
    (a : EuclideanSpace ℂ (Fin (m + 1))) (ha : a ≠ 0) :
    ∃ U : EuclideanSpace ℂ (Fin (m + 1)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (m + 1)),
      U a = ‖a‖ • complexFirstBasisVector m ∧
      (stdGaussian (EuclideanSpace ℂ (Fin (m + 1)))).map U =
        stdGaussian (EuclideanSpace ℂ (Fin (m + 1))) := by
  obtain ⟨U, hU⟩ := exists_complex_nonzero_frame m a ha
  exact ⟨U, hU, stdGaussian_map (complexFrameToReal U)⟩

theorem complex_unit_frame_first_coordinate {m : ℕ}
    (a v : EuclideanSpace ℂ (Fin (m + 1)))
    (U : EuclideanSpace ℂ (Fin (m + 1)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (m + 1)))
    (hU : U a = complexFirstBasisVector m) :
    U v 0 = inner ℂ a v := by
  have h := U.inner_map_map a v
  rw [hU] at h
  simpa [complexFirstBasisVector, EuclideanSpace.inner_single_left] using h

end
end JinWishart

#print axioms JinWishart.exists_complex_unit_frame
#print axioms JinWishart.exists_complex_nonzero_frame
#print axioms JinWishart.exists_complex_nonzero_gaussian_frame
#print axioms JinWishart.complex_unit_frame_first_coordinate
