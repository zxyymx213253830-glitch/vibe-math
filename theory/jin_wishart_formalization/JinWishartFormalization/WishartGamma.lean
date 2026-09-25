import JinWishartFormalization.WishartProbability
import JinWishartFormalization.GaussianRadialCDF

open MeasureTheory ProbabilityTheory

namespace JinWishart

/-- The energy in an `m × 1` central complex Gaussian sample is Gamma with
shape `m` and unit rate. This is the scalar Gram/Wishart law before passing
through the smallest-eigenvalue map. -/
theorem centralColumnSampleEnergy_map_eq_gammaMeasure {m : ℕ} (hm : 0 < m) :
    (stdGaussian (ComplexSample (m := m) (n := 1))).map
      centralColumnSampleEnergy = gammaMeasure (m : ℝ) 1 := by
  letI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  letI : Nontrivial (EuclideanSpace ℝ ((Fin m × Fin 1) × Fin 2)) := inferInstance
  have henergy : centralColumnSampleEnergy =
      euclideanGaussianEnergy (ι := ((Fin m × Fin 1) × Fin 2)) := by
    funext x
    exact centralColumnSampleEnergy_eq_euclideanEnergy x
  rw [henergy]
  apply stdGaussian_euclideanEnergy_map_eq_gammaMeasure m ?_ hm
  simp
  omega

/-- The smallest eigenvalue of the central one-column Wishart sample has the
same integer-shape Gamma law. -/
theorem centralColumnSmallestEigenvalue_map_eq_gammaMeasure {m : ℕ} (hm : 0 < m) :
    (stdGaussian (ComplexSample (m := m) (n := 1))).map
      (complexNoncentralSampleSmallestEigenvalue (0 : Matrix (Fin m) (Fin 1) ℂ)
        (by norm_num)) = gammaMeasure (m : ℝ) 1 := by
  have hfun : complexNoncentralSampleSmallestEigenvalue
      (0 : Matrix (Fin m) (Fin 1) ℂ) (by norm_num) = centralColumnSampleEnergy := by
    funext x
    exact centralColumnSampleSmallestEigenvalue_eq_energy hm x
  rw [hfun, centralColumnSampleEnergy_map_eq_gammaMeasure hm]

end JinWishart
