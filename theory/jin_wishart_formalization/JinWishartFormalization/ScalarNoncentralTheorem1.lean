import JinWishartFormalization.NuttallQRiceNormalization
import JinWishartFormalization.NuttallQRiceMass
import JinWishartFormalization.ScalarNoncentralCDFRice

/-!
# Noncentral scalar Theorem 1

The Rice radial kernel has unit total mass.  This normalizes the order-zero
Nuttall-Q tail, closing one of the analytic obligations for the scalar
specialization of Theorem 1.
-/

open Matrix MeasureTheory ProbabilityTheory Set

namespace JinWishart

/-- For every nonnegative noncentrality amplitude, the scalar Nuttall-Q
tail at zero is one. -/
theorem nuttallQ_10_zero_eq_one (a : ℝ) (ha : 0 ≤ a) :
    nuttallQ 1 0 a 0 = 1 := by
  rw [nuttallQ_10_eq_realRiceTail,
    riceRadialKernel_integral_eq_one a ha]
  norm_num

/-- The scalar Theorem 1 probability formula now needs only the
integrability of the complex Nuttall-Q kernel. -/
theorem noncentralScalarCDF_eq_theorem1Candidate_of_integrable
    (M : Matrix (Fin 1) (Fin 1) ℂ) (x : ℝ) (hx : 0 ≤ x)
    (hint : IntegrableOn
      (nuttallQIntegrand 1 0 ‖complexSampleMean M‖) (Ioi 0)) :
    cdf ((stdGaussian (ComplexSample (m := 1) (n := 1))).map
      (complexNoncentralSampleSmallestEigenvalue M (by norm_num))) x =
      theorem1CdfCandidate 1 1 1 (by omega) (by omega)
        (fun _ : Fin 1 => ‖M 0 0‖ ^ 2) x := by
  exact noncentralScalarCDF_eq_theorem1Candidate_of_Q_normalized
    M x hx hint (nuttallQ_10_zero_eq_one _ (norm_nonneg _))

/-- The noncentral `1 × 1` specialization of Theorem 1 equals the CDF of
the actual complex Gaussian Gram eigenvalue, without analytic side
conditions. -/
theorem noncentralScalarCDF_eq_theorem1Candidate
    (M : Matrix (Fin 1) (Fin 1) ℂ) (x : ℝ) (hx : 0 ≤ x) :
    cdf ((stdGaussian (ComplexSample (m := 1) (n := 1))).map
      (complexNoncentralSampleSmallestEigenvalue M (by norm_num))) x =
      theorem1CdfCandidate 1 1 1 (by omega) (by omega)
        (fun _ : Fin 1 => ‖M 0 0‖ ^ 2) x := by
  exact noncentralScalarCDF_eq_theorem1Candidate_of_integrable M x hx
    (nuttallQ_10_integrand_integrableOn_Ioi _ (norm_nonneg _))

end JinWishart
