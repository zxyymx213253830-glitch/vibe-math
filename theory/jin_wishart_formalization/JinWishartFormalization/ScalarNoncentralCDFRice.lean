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

/-- The `(1,0)` Nuttall-Q tail is the complex embedding of a real Rice
tail integral. -/
theorem nuttallQ_10_eq_realRiceTail (a b : ℝ) :
    nuttallQ 1 0 a b =
      ((∫ t in Ioi b, riceRadialKernel a t : ℝ) : ℂ) := by
  unfold nuttallQ
  have hpoint (t : ℝ) :
      nuttallQIntegrand 1 0 a t = (riceRadialKernel a t : ℂ) := by
    simp only [nuttallQIntegrand, riceRadialKernel, pow_one]
    rw [← modifiedBesselI_zero_ofReal_eq_realSeries]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => hpoint t)]
  exact integral_complex_ofReal

/-- The Rice radial kernel is nonnegative at positive radii. -/
theorem riceRadialKernel_nonneg (a t : ℝ) (ht : 0 ≤ t) :
    0 ≤ riceRadialKernel a t := by
  unfold riceRadialKernel
  exact mul_nonneg (mul_nonneg ht (Real.exp_nonneg _))
    (besselI0RealSeries_nonneg (a * t))

/-- The Nuttall-Q tail is real and nonnegative when its lower cutoff is
nonnegative. -/
theorem nuttallQ_10_nonneg_real (a b : ℝ) (hb : 0 ≤ b) :
    ∃ q : ℝ, 0 ≤ q ∧ nuttallQ 1 0 a b = (q : ℂ) := by
  refine ⟨∫ t in Ioi b, riceRadialKernel a t, ?_, nuttallQ_10_eq_realRiceTail a b⟩
  apply setIntegral_nonneg measurableSet_Ioi
  intro t ht
  exact riceRadialKernel_nonneg a t (le_trans hb (le_of_lt ht))

/-- Conditional scalar specialization of the paper's Theorem 1. The two
assumptions are exactly the remaining analytic facts: improper-tail
integrability and total Rice mass one. -/
theorem noncentralScalarCDF_eq_theorem1Candidate_of_Q_normalized
    (M : Matrix (Fin 1) (Fin 1) ℂ) (x : ℝ) (hx : 0 ≤ x)
    (hint : IntegrableOn
      (nuttallQIntegrand 1 0 ‖complexSampleMean M‖) (Ioi 0))
    (hQ : nuttallQ 1 0 ‖complexSampleMean M‖ 0 = 1) :
    cdf ((stdGaussian (ComplexSample (m := 1) (n := 1))).map
      (complexNoncentralSampleSmallestEigenvalue M (by norm_num))) x =
      theorem1CdfCandidate 1 1 1 (by omega) (by omega)
        (fun _ : Fin 1 => ‖M 0 0‖ ^ 2) x := by
  let R : ℝ := Real.sqrt (2 * x)
  obtain ⟨q, hq, hqeq⟩ :=
    nuttallQ_10_nonneg_real ‖complexSampleMean M‖ R (Real.sqrt_nonneg _)
  have hdiff := noncentralScalarCDF_eq_nuttallQ_difference M x hx hint
  rw [hQ, hqeq] at hdiff
  have hreal :
      cdf ((stdGaussian (ComplexSample (m := 1) (n := 1))).map
        (complexNoncentralSampleSmallestEigenvalue M (by norm_num))) x = 1 - q := by
    apply Complex.ofReal_injective
    simpa using hdiff
  rw [theorem1ScalarCandidate_uses_shiftNorm M x, hQ, hqeq]
  simp [hreal, abs_of_nonneg hq]

end

end JinWishart
