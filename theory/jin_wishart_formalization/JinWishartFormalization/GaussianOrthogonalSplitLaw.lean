import JinWishartFormalization.GaussianOrthogonalProjectionLaw
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-! Actual Gaussian product law of a fixed orthogonal splitting.
[需人工审查] Conditional use with random preceding columns is not asserted. -/
open MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem stdGaussian_orthogonal_split_indep (K : Submodule ℝ E) :
    IndepFun K.orthogonalProjectionOnto Kᗮ.orthogonalProjectionOnto (stdGaussian E) := by
  let L := K.orthogonalProjectionOnto.prod Kᗮ.orthogonalProjectionOnto
  have hG : HasGaussianLaw
      (fun z : E => (K.orthogonalProjectionOnto z, Kᗮ.orthogonalProjectionOnto z))
      (stdGaussian E) := by
    exact (IsGaussian.hasGaussianLaw_id (μ := stdGaussian E)).map_of_measurable L (by fun_prop)
  apply hG.indepFun_of_covariance_inner
  intro x y
  have h1 : (fun z : E => inner ℝ x (K.orthogonalProjectionOnto z)) =
      (fun z => inner ℝ (x : E) z) := by
    funext z
    rw [← K.orthogonalProjectionOnto.adjoint_inner_left, K.adjoint_orthogonalProjectionOnto]
    rfl
  have h2 : (fun z : E => inner ℝ y (Kᗮ.orthogonalProjectionOnto z)) =
      (fun z => inner ℝ (y : E) z) := by
    funext z
    rw [← Kᗮ.orthogonalProjectionOnto.adjoint_inner_left, Kᗮ.adjoint_orthogonalProjectionOnto]
    rfl
  rw [h1, h2, ← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
    covarianceBilin_stdGaussian, innerSL_apply_apply]
  exact y.property x x.property

theorem stdGaussian_orthogonal_split_law (K : Submodule ℝ E) :
    (stdGaussian E).map (fun z =>
      (K.orthogonalProjectionOnto z, Kᗮ.orthogonalProjectionOnto z)) =
      (stdGaussian K).prod (stdGaussian Kᗮ) := by
  rw [(stdGaussian_orthogonal_split_indep K).map_prod_eq_prod_map_map
    (by fun_prop) (by fun_prop), stdGaussian_orthogonalProjectionOnto_law,
    stdGaussian_orthogonalProjectionOnto_law]

end
end JinWishart
#print axioms JinWishart.stdGaussian_orthogonal_split_indep
#print axioms JinWishart.stdGaussian_orthogonal_split_law
