import JinWishartFormalization.GaussianGramProjector
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finrank

#check Matrix.toLpLin_mul_same
#check Matrix.toLpLin_one
#check Matrix.toEuclideanLin
#check LinearMap.finrank_range_of_inj
#check finrank_real_of_complex
#check Submodule.restrictScalarsEquiv
#check LinearEquiv.restrictScalars
#check finrank_euclideanSpace_fin
#check Function.LeftInverse.injective

open Matrix
namespace JinWishart
noncomputable section

-- Codex probe: compile before using it in the final joint module.
theorem rank_probe_leftInverse {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (hA : IsUnit (Aᴴ * A).det) :
    Function.LeftInverse (((Aᴴ * A)⁻¹ * Aᴴ).toEuclideanLin) A.toEuclideanLin := by
  intro x
  have hmat : ((Aᴴ * A)⁻¹ * Aᴴ) * A = 1 := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA]
  have h := congrArg (fun B : Matrix (Fin n) (Fin n) ℂ => B.toEuclideanLin x) hmat
  simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
    LinearMap.comp_apply, Matrix.toLpLin_one, LinearMap.id_apply] using h

end
end JinWishart
