import JinWishartFormalization.ScalarNoncentralPolar

/-!
# Set-integral form of the scalar angular Bessel identity

This module translates the interval-integral angular identity into the open
angle interval used by Mathlib's polar-coordinate chart.
-/

open MeasureTheory Set

namespace JinWishart

/-- The Gaussian angular integral over the polar chart's open angle interval
is the real part of the complex order-zero Bessel expression.  The conversion
from the interval integral uses that the two endpoint singletons have zero
Lebesgue measure. -/
theorem polarGaussian_angleSetIntegral_eq_besselI0_re (r c : ℝ) :
    (∫ θ in Ioo (-Real.pi) Real.pi,
      Real.exp (-(‖(r : ℂ) * (Real.cos θ + Real.sin θ * Complex.I) -
        (c : ℂ)‖ ^ 2) / 2)) =
      ((2 * Real.pi : ℂ) *
        (Real.exp (-((r ^ 2 + c ^ 2) / 2)) : ℂ) *
          modifiedBesselI 0 ((r * c : ℝ) : ℂ)).re := by
  have hinterval :
      (∫ θ in Ioo (-Real.pi) Real.pi,
        Real.exp (-(‖(r : ℂ) * (Real.cos θ + Real.sin θ * Complex.I) -
          (c : ℂ)‖ ^ 2) / 2)) =
        ∫ θ in (-Real.pi)..Real.pi,
          Real.exp (-(‖(r : ℂ) * (Real.cos θ + Real.sin θ * Complex.I) -
            (c : ℂ)‖ ^ 2) / 2) := by
    symm
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
      integral_Ioc_eq_integral_Ioo]
  rw [hinterval]
  have hbessel := polarGaussian_angularIntegral_eq_besselI0 (r := r) (c := c)
  have hre := congrArg Complex.re hbessel
  simpa only [Complex.ofReal_re] using hre

end JinWishart
