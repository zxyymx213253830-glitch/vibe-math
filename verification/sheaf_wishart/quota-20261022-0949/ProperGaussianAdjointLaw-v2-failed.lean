import JinWishartFormalization.GaussianMatrixPolynomialLaw
import JinWishartFormalization.GaussianMatrixBlockLaw

/-! Proper CN(0,1) conjugation and adjoint laws, including fixed mean and empty
dimensions. Codex proofs. [需人工审查] Product pushforward, variance and later
use in the wide inverse-moment branch. No rectangular projection law here. -/
open Matrix MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

theorem standardComplexScalarLaw_map_conj :
    standardComplexScalarLaw.map (star : ℂ → ℂ) = standardComplexScalarLaw := by
  have hu := stdGaussian_map Complex.conjLIE
  have hU : (Complex.conjLIE : ℂ → ℂ) = star := rfl
  rw [hU] at hu
  unfold standardComplexScalarLaw
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have he : (star : ℂ → ℂ) ∘ (fun z => (Real.sqrt 2)⁻¹ • z) =
      (fun z => (Real.sqrt 2)⁻¹ • z) ∘ (star : ℂ → ℂ) := by
    funext z
    simp
  rw [he, ← Measure.map_map (by fun_prop) (by fun_prop), hu]

theorem standardComplexPiLaw_map_conj {ι : Type*} [Fintype ι] :
    (standardComplexPiLaw ι).map (fun z i => star (z i)) = standardComplexPiLaw ι := by
  unfold standardComplexPiLaw
  rw [Measure.pi_map_pi (fun _ => (by fun_prop))]
  simp_rw [standardComplexScalarLaw_map_conj]

private theorem matrixLawEntries {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) :
    complexGaussianMatrixLaw M = (standardComplexPiLaw (Fin m × Fin n)).map
      (fun z i j => z (i,j) + M i j) := by
  rw [← complexMatrixEntries_law m n,
    Measure.map_map (by fun_prop) (measurable_complexMatrixEntries m n)]
  rfl

theorem complexGaussianMatrixLaw_conjugate {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) :
    (complexGaussianMatrixLaw M).map (fun X => X.map star) =
      complexGaussianMatrixLaw (M.map star) := by
  rw [matrixLawEntries M]
  erw [Measure.map_map (by fun_prop) (by fun_prop)]
  have he : (fun X : Matrix (Fin m) (Fin n) ℂ => X.map star) ∘
      (fun z i j => z (i,j) + M i j) =
      (fun z i j => z (i,j) + (M.map star) i j) ∘ (fun z ij => star (z ij)) := by
    funext z
    ext i j
    simp [Function.comp_def]
  rw [he, ← Measure.map_map (by fun_prop) (by fun_prop), standardComplexPiLaw_map_conj]
  exact (matrixLawEntries _).symm

private theorem shiftedTranspose {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) :
    (complexGaussianMatrixLaw M).map Matrix.transpose = complexGaussianMatrixLaw Mᵀ := by
  unfold complexGaussianMatrixLaw
  rw [Measure.map_map (by fun_prop) (measurable_shiftedComplexSampleMatrix _)]
  have he : Matrix.transpose ∘ (fun z : ComplexSample (m := m) (n := n) =>
      complexSampleMatrix z + M) =
      (fun z => complexSampleMatrix z + Mᵀ) ∘ complexSampleTransposeReindex m n := by
    funext z
    simp only [Function.comp_def, complexSampleMatrix_transpose_reindex, transpose_add]
  rw [he, ← Measure.map_map (measurable_shiftedComplexSampleMatrix _)
    (complexSampleTransposeReindex m n).continuous.measurable, stdGaussian_map]

theorem complexGaussianMatrixLaw_conjTranspose {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) :
    (complexGaussianMatrixLaw M).map Matrix.conjTranspose = complexGaussianMatrixLaw Mᴴ := by
  have he : (Matrix.conjTranspose : Matrix (Fin m) (Fin n) ℂ → _) =
      Matrix.transpose ∘ (fun X => X.map star) := rfl
  rw [he, ← Measure.map_map (by fun_prop) (by fun_prop),
    complexGaussianMatrixLaw_conjugate, shiftedTranspose]
  rfl

end
end JinWishart
#print axioms JinWishart.standardComplexScalarLaw_map_conj
#print axioms JinWishart.standardComplexPiLaw_map_conj
#print axioms JinWishart.complexGaussianMatrixLaw_conjugate
#print axioms JinWishart.complexGaussianMatrixLaw_conjTranspose
