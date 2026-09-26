import JinWishartFormalization.ScalarNoncentralTheorem1

/-!
# Local small-threshold structure for the scalar noncentral law

This module records the analytic local ingredient for the scalar `x -> 0`
asymptotic.  The remaining step is an interval-average limit for a continuous
factor; it is intentionally not postulated here.
-/

open Matrix MeasureTheory ProbabilityTheory Set

namespace JinWishart

noncomputable section

/-- The continuous factor left after extracting the radial Jacobian from the
Rice kernel. -/
def riceRadialFactor (a t : ℝ) : ℝ :=
  Real.exp (-((t ^ 2 + a ^ 2) / 2)) *
    (modifiedBesselI 0 ((a * t : ℝ) : ℂ)).re

/-- The Rice kernel is radius times its continuous local factor. -/
theorem riceRadialKernel_eq_radius_mul_factor (a t : ℝ) :
    riceRadialKernel a t = t * riceRadialFactor a t := by
  unfold riceRadialKernel riceRadialFactor
  have h := modifiedBesselI_zero_ofReal_eq_realSeries (a * t)
  have hre := congrArg Complex.re h
  have hseries :
      (∑' n : ℕ, ((a * t) ^ 2 / 4) ^ n / ((n.factorial : ℝ) ^ 2)) =
        (modifiedBesselI 0 ((a * t : ℝ) : ℂ)).re := by
    simpa using hre
  rw [hseries]
  ring

/-- The local Rice factor is continuous, so its value at zero determines the
leading radial coefficient. -/
theorem continuous_riceRadialFactor (a : ℝ) :
    Continuous (riceRadialFactor a) := by
  unfold riceRadialFactor
  apply (Real.continuous_exp.comp (by fun_prop)).mul
  exact Complex.continuous_re.comp
    ((continuous_modifiedBesselI 0).comp (by fun_prop))

/-- The local Rice factor at radius zero is the Gaussian penalty associated
with the noncentrality amplitude. -/
theorem riceRadialFactor_zero (a : ℝ) :
    riceRadialFactor a 0 = Real.exp (-(a ^ 2 / 2)) := by
  simp [riceRadialFactor, modifiedBesselI_zero]

/-- In the scalar complex Wishart specialization, the local coefficient is
`exp (-lambda)` for `lambda = ||M₀₀||²`. -/
theorem riceRadialFactor_zero_eq_exp_neg_noncentrality
    (M : Matrix (Fin 1) (Fin 1) ℂ) :
    riceRadialFactor ‖complexSampleMean M‖ 0 =
      Real.exp (-‖M 0 0‖ ^ 2) := by
  rw [riceRadialFactor_zero]
  rw [complexSampleMean_norm_sq_scalar]
  congr 1
  ring

/-- Exact finite-radius representation with the Jacobian made explicit.
This reduces the desired small-`x` limit to a one-dimensional local integral
average of `riceRadialFactor`. -/
theorem noncentralScalarCDF_eq_radius_factorIntegral
    (M : Matrix (Fin 1) (Fin 1) ℂ) (x : ℝ) (hx : 0 ≤ x) :
    cdf ((stdGaussian (ComplexSample (m := 1) (n := 1))).map
      (complexNoncentralSampleSmallestEigenvalue M (by norm_num))) x =
      ∫ r in Ioc (0 : ℝ) (Real.sqrt (2 * x)),
        r * riceRadialFactor ‖complexSampleMean M‖ r := by
  rw [noncentralScalarCDF_eq_riceRadialIntegral M x hx]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r _
  exact riceRadialKernel_eq_radius_mul_factor _ _

end

end JinWishart
