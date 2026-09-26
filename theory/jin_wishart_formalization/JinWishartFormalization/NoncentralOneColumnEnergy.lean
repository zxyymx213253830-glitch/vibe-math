import JinWishartFormalization.WishartProbability
import JinWishartFormalization.GaussianEuclideanBallDensity
import Mathlib.Probability.CDF

/-!
# Noncentral one-column Wishart samples as shifted Gaussian energy

For a single column, the only Gram eigenvalue is the squared Euclidean norm
of the shifted real Gaussian coordinates divided by two.  This module makes
that model-to-event bridge explicit for every positive number of rows.
-/

open MeasureTheory ProbabilityTheory Set

namespace JinWishart

/-- The least eigenvalue of a noncentral one-column complex Gram sample is its
shifted real Gaussian energy. -/
theorem complexNoncentralColumnSmallestEigenvalue_eq_shiftedEnergy
    {m : ℕ} (hm : 0 < m) (M : Matrix (Fin m) (Fin 1) ℂ)
    (z : ComplexSample (m := m) (n := 1)) :
    complexNoncentralSampleSmallestEigenvalue M (by norm_num)
        (x := z) = ‖z + complexSampleMean M‖ ^ 2 / 2 := by
  have hshift :
      complexNoncentralSampleSmallestEigenvalue M (by norm_num) z =
        complexNoncentralSampleSmallestEigenvalue (0 : Matrix (Fin m) (Fin 1) ℂ)
          (by norm_num) (z + complexSampleMean M) := by
    simp [complexNoncentralSampleSmallestEigenvalue, complexSampleMatrix_add_mean]
  rw [hshift, centralColumnSampleSmallestEigenvalue_eq_energy hm]
  rw [centralColumnSampleEnergy_eq_euclideanEnergy]

/-- The actual noncentral one-column eigenvalue sublevel event is the closed
ball around the negative mean in its underlying real Gaussian space. -/
theorem noncentralColumnSmallestEigenvalue_sublevelMass_eq_shiftedBall
    {m : ℕ} (hm : 0 < m) (M : Matrix (Fin m) (Fin 1) ℂ)
    (x : ℝ) (hx : 0 ≤ x) :
    (stdGaussian (ComplexSample (m := m) (n := 1))).map
        (complexNoncentralSampleSmallestEigenvalue M (by norm_num)) (Iic x) =
      stdGaussian (ComplexSample (m := m) (n := 1))
        (Metric.closedBall (-complexSampleMean M) (Real.sqrt (2 * x))) := by
  rw [Measure.map_apply
    (measurable_complexNoncentralSampleSmallestEigenvalue M (by norm_num))
    measurableSet_Iic]
  have hfun : complexNoncentralSampleSmallestEigenvalue M (by norm_num) =
      fun z ↦ ‖z + complexSampleMean M‖ ^ 2 / 2 := by
    funext z
    exact complexNoncentralColumnSmallestEigenvalue_eq_shiftedEnergy hm M z
  rw [hfun]
  congr 1
  ext z
  simp only [Set.mem_preimage, Set.mem_Iic, Metric.mem_closedBall,
    dist_eq_norm, sub_neg_eq_add]
  have hR : 0 ≤ Real.sqrt (2 * x) := Real.sqrt_nonneg _
  have hr : Real.sqrt (2 * x) ^ 2 = 2 * x :=
    Real.sq_sqrt (by positivity)
  constructor
  · intro hz
    have hn : 0 ≤ ‖z + complexSampleMean M‖ := norm_nonneg _
    apply (sq_le_sq₀ hn hR).mp
    nlinarith
  · intro hz
    have hn : 0 ≤ ‖z + complexSampleMean M‖ := norm_nonneg _
    have hsq := (sq_le_sq₀ hn hR).mpr hz
    nlinarith

/-- The noncentral one-column CDF is an explicit shifted Gaussian Lebesgue
integral over the corresponding real-coordinate ball. -/
theorem noncentralColumnCDF_eq_shiftedGaussianDensityIntegral
    {m : ℕ} (hm : 0 < m) (M : Matrix (Fin m) (Fin 1) ℂ)
    (x : ℝ) (hx : 0 ≤ x) :
    cdf ((stdGaussian (ComplexSample (m := m) (n := 1))).map
        (complexNoncentralSampleSmallestEigenvalue M (by norm_num))) x =
      ∫ z in Metric.closedBall (0 : ComplexSample (m := m) (n := 1))
          (Real.sqrt (2 * x)),
        (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card
            (((Fin m × Fin 1) × Fin 2)) *
          Real.exp (-‖z - complexSampleMean M‖ ^ 2 / 2) := by
  rw [cdf_eq_real, measureReal_def]
  rw [noncentralColumnSmallestEigenvalue_sublevelMass_eq_shiftedBall hm M x hx]
  rw [← measureReal_def]
  rw [stdGaussian_euclidean_ball_real_eq_densityIntegral]
  rw [integral_euclideanGaussian_shiftedBall_eq_centered]

end JinWishart
