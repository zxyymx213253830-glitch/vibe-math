import JinWishartFormalization.ScalarGaussianComplexBridge
import JinWishartFormalization.ScalarComplexCenterDisk
import JinWishartFormalization.NuttallQRiceSplit

/-!
# Scalar noncentral Wishart CDF as a Rice radial integral

This module combines the actual Gaussian probability model with the
complex-center polar integral and the scalar Nuttall-Q kernel.
-/

open Matrix MeasureTheory ProbabilityTheory Set

namespace JinWishart

noncomputable section

theorem scalarComplexMean_norm_eq_sampleMean_norm
    (M : Matrix (Fin 1) (Fin 1) ℂ) :
    ‖(Real.sqrt 2 : ℂ) * M 0 0‖ = ‖complexSampleMean M‖ := by
  rw [← centralScalarToComplex_complexSampleMean]
  exact centralScalarToComplex.norm_map _

/-- The actual `1 × 1` noncentral Wishart CDF is a finite Rice radial
integral with amplitude equal to the Euclidean Gaussian mean. -/
theorem noncentralScalarCDF_eq_riceRadialIntegral
    (M : Matrix (Fin 1) (Fin 1) ℂ) (x : ℝ) (hx : 0 ≤ x) :
    cdf ((stdGaussian (ComplexSample (m := 1) (n := 1))).map
      (complexNoncentralSampleSmallestEigenvalue M (by norm_num))) x =
      ∫ r in Ioc (0 : ℝ) (Real.sqrt (2 * x)),
        riceRadialKernel ‖complexSampleMean M‖ r := by
  rw [noncentralScalarCDF_eq_complexGaussianDiskIntegral M x hx]
  rw [integral_const_mul]
  rw [integral_shiftedGaussian_complex_closedBall_eq_riceRadial
    ((Real.sqrt 2 : ℂ) * M 0 0) (Real.sqrt (2 * x)) (Real.sqrt_nonneg _)]
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r _
  rw [scalarComplexMean_norm_eq_sampleMean_norm M]
  dsimp only
  rw [← modifiedBesselI_zero_ofReal_eq_realSeries]
  simp [riceRadialKernel, Real.pi_ne_zero, mul_assoc, mul_comm, mul_left_comm]

/-- Subject to the explicit improper-integrability assumption, the CDF is
the difference of two `(1,0)` Nuttall-Q tails. -/
theorem noncentralScalarCDF_eq_nuttallQ_difference
    (M : Matrix (Fin 1) (Fin 1) ℂ) (x : ℝ) (hx : 0 ≤ x)
    (hint : IntegrableOn
      (nuttallQIntegrand 1 0 ‖complexSampleMean M‖) (Ioi 0)) :
    ((cdf ((stdGaussian (ComplexSample (m := 1) (n := 1))).map
      (complexNoncentralSampleSmallestEigenvalue M (by norm_num))) x : ℝ) : ℂ) =
      nuttallQ 1 0 ‖complexSampleMean M‖ 0 -
        nuttallQ 1 0 ‖complexSampleMean M‖ (Real.sqrt (2 * x)) := by
  rw [noncentralScalarCDF_eq_riceRadialIntegral M x hx]
  rw [← intervalIntegral.integral_of_le (Real.sqrt_nonneg (2 * x))]
  exact (nuttallQ_10_zero_sub_eq_riceIntegral
    ‖complexSampleMean M‖ (Real.sqrt (2 * x)) (Real.sqrt_nonneg _) hint).symm

end

end JinWishart
