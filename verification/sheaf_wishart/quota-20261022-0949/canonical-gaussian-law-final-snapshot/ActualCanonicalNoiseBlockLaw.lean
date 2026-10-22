import JinWishartFormalization.GaussianDisjointMatrixBlockLaw

/-! Actual same-source proper-CN1 law of fixed isometric noise coordinates
and arbitrary disjoint row blocks with a fixed mean. Codex.
[需人工审查] Pushforward composition and application to canonical models. -/
open Matrix MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

theorem actual_isometric_noise_disjoint_row_blocks {m p b a c : ℕ}
    (U : Matrix (Fin p) (Fin b) ℂ) (hU : Uᴴ*U=1)
    (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m))
    (M : Matrix (Fin m) (Fin b) ℂ) (e : Fin a → Fin m) (f : Fin c → Fin m)
    (h : Function.Injective (Sum.elim e f)) :
    (stdGaussian (ComplexSample (m := m) (n := p))).map
      (fun z => ((unitaryActColumns V (complexSampleMatrix z*U)+M).submatrix e id,
        (unitaryActColumns V (complexSampleMatrix z*U)+M).submatrix f id))=
      (complexGaussianMatrixLaw (M.submatrix e id)).prod
        (complexGaussianMatrixLaw (M.submatrix f id)) := by
  let F := fun Z : Matrix (Fin m) (Fin p) ℂ => unitaryActColumns V (Z*U)
  let P := fun A : Matrix (Fin m) (Fin b) ℂ => (A.submatrix e id,A.submatrix f id)
  let S := fun A : Matrix (Fin m) (Fin b) ℂ => A+M
  let g := fun z : ComplexSample (m := m) (n := p) => complexSampleMatrix z+0
  have hmul : Measurable (fun Z : Matrix (Fin m) (Fin p) ℂ => Z*U) :=
    (continuous_id.matrix_mul continuous_const).measurable
  have hF : Measurable F := (measurable_unitaryActColumns V).comp hmul
  have hP : Measurable P := by unfold P; fun_prop
  have hS : Measurable S := by unfold S; fun_prop
  have hg : Measurable g := measurable_shiftedComplexSampleMatrix _
  have hlaw : (complexGaussianMatrixLaw (0 : Matrix (Fin m) (Fin p) ℂ)).map F=
      complexGaussianMatrixLaw (0 : Matrix (Fin m) (Fin b) ℂ) := by
    change (complexGaussianMatrixLaw (0 : Matrix (Fin m) (Fin p) ℂ)).map
      (unitaryActColumns V ∘ (fun Z => Z*U)) = _
    rw [← Measure.map_map (measurable_unitaryActColumns V) hmul,
      complexGaussianMatrixLaw_right_isometric_projection U hU,
      complexGaussianMatrixLaw_unitary_invariant]
  have hshift : (complexGaussianMatrixLaw (0 : Matrix (Fin m) (Fin b) ℂ)).map S=
      complexGaussianMatrixLaw M := by
    unfold complexGaussianMatrixLaw
    rw [Measure.map_map hS (measurable_shiftedComplexSampleMatrix _)]
    congr 1
    funext z
    simp only [Function.comp_def,S,add_zero]
  have he : (fun z : ComplexSample (m := m) (n := p) =>
      ((unitaryActColumns V (complexSampleMatrix z*U)+M).submatrix e id,
        (unitaryActColumns V (complexSampleMatrix z*U)+M).submatrix f id)) =
      (P ∘ S ∘ F) ∘ g := by
    funext z
    simp only [Function.comp_def,P,S,F,g,add_zero]
  erw [he,← Measure.map_map (hP.comp (hS.comp hF)) hg]
  change (complexGaussianMatrixLaw (0 : Matrix (Fin m) (Fin p) ℂ)).map (P ∘ S ∘ F)=_
  erw [← Measure.map_map (hP.comp hS) hF,hlaw,
    ← Measure.map_map hP hS,hshift]
  exact complexGaussianMatrixLaw_disjoint_rows M e f h

end
end JinWishart
#print axioms JinWishart.actual_isometric_noise_disjoint_row_blocks
