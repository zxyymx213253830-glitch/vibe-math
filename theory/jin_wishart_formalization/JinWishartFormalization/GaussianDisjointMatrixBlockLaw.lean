import JinWishartFormalization.GaussianRectangularFrameLaw
import JinWishartFormalization.GaussianDisjointPrincipalLaw

/-! Full shifted-matrix block product laws for arbitrary fixed disjoint
selectors. Reuses the existing raw Gaussian disjoint-column law and adjoint
law. Codex. [需人工审查] Product pushforwards and proper variance convention. -/
open Matrix MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

theorem complexGaussianMatrixLaw_disjoint_columns {m n k l : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (e : Fin k → Fin n) (f : Fin l → Fin n)
    (h : Function.Injective (Sum.elim e f)) :
    (complexGaussianMatrixLaw M).map (fun A => (A.submatrix id e,A.submatrix id f))=
      (complexGaussianMatrixLaw (M.submatrix id e)).prod
        (complexGaussianMatrixLaw (M.submatrix id f)) := by
  let Fe := fun z : ComplexSample (m := m) (n := k) =>
    complexSampleMatrix z+M.submatrix id e
  let Ff := fun z : ComplexSample (m := m) (n := l) =>
    complexSampleMatrix z+M.submatrix id f
  have hFe : Measurable Fe := measurable_shiftedComplexSampleMatrix _
  have hFf : Measurable Ff := measurable_shiftedComplexSampleMatrix _
  have hS : Measurable (fun z : ComplexSample (m := m) (n := n) =>
      (sampleColumnSelection e z,sampleColumnSelection f z)) :=
    (measurable_sampleColumnSelection e).prodMk (measurable_sampleColumnSelection f)
  have hs := congrArg (fun μ => μ.map (Prod.map Fe Ff))
    (stdGaussian_disjoint_columnSelections (m := m) e f h)
  rw [Measure.map_map (hFe.prodMap hFf) hS,
    ← Measure.map_prod_map _ _ hFe hFf] at hs
  have he : Prod.map Fe Ff ∘ (fun z : ComplexSample (m := m) (n := n) =>
      (sampleColumnSelection e z,sampleColumnSelection f z)) =
      (fun A : Matrix (Fin m) (Fin n) ℂ => (A.submatrix id e,A.submatrix id f)) ∘
        (fun z => complexSampleMatrix z+M) := by
    funext z
    apply Prod.ext <;> ext i j <;> rfl
  have hG : Measurable (fun A : Matrix (Fin m) (Fin n) ℂ =>
      (A.submatrix id e,A.submatrix id f)) := by fun_prop
  rw [he,← Measure.map_map hG (measurable_shiftedComplexSampleMatrix M)] at hs
  exact hs

theorem complexGaussianMatrixLaw_disjoint_rows {m n a c : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (e : Fin a → Fin m) (f : Fin c → Fin m)
    (h : Function.Injective (Sum.elim e f)) :
    (complexGaussianMatrixLaw M).map (fun A => (A.submatrix e id,A.submatrix f id))=
      (complexGaussianMatrixLaw (M.submatrix e id)).prod
        (complexGaussianMatrixLaw (M.submatrix f id)) := by
  let C := fun A : Matrix (Fin n) (Fin m) ℂ => (A.submatrix id e,A.submatrix id f)
  let Q := Prod.map
    (Matrix.conjTranspose : Matrix (Fin n) (Fin a) ℂ → Matrix (Fin a) (Fin n) ℂ)
    (Matrix.conjTranspose : Matrix (Fin n) (Fin c) ℂ → Matrix (Fin c) (Fin n) ℂ)
  have hC : Measurable C := by unfold C; fun_prop
  have hQ : Measurable Q := (by fun_prop : Measurable
      (Matrix.conjTranspose : Matrix (Fin n) (Fin a) ℂ → _)).prodMap
        (by fun_prop : Measurable (Matrix.conjTranspose : Matrix (Fin n) (Fin c) ℂ → _))
  have hs := congrArg (fun μ => μ.map Q)
    (complexGaussianMatrixLaw_disjoint_columns Mᴴ e f h)
  rw [Measure.map_map hQ hC,
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)] at hs
  have he : Q ∘ C =
      (fun A : Matrix (Fin m) (Fin n) ℂ => (A.submatrix e id,A.submatrix f id)) ∘
        Matrix.conjTranspose := by
    funext A
    apply Prod.ext <;> ext i j <;> rfl
  have hG : Measurable (fun A : Matrix (Fin m) (Fin n) ℂ =>
      (A.submatrix e id,A.submatrix f id)) := by fun_prop
  rw [he,← Measure.map_map hG (by fun_prop),complexGaussianMatrixLaw_conjTranspose,
    complexGaussianMatrixLaw_conjTranspose,complexGaussianMatrixLaw_conjTranspose] at hs
  simpa only [Matrix.conjTranspose_conjTranspose,Matrix.conjTranspose_submatrix] using hs

end
end JinWishart
#print axioms JinWishart.complexGaussianMatrixLaw_disjoint_columns
#print axioms JinWishart.complexGaussianMatrixLaw_disjoint_rows
