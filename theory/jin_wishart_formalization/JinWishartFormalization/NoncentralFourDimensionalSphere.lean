import JinWishartFormalization.BesselI1Angle

/-!
# Four-dimensional spherical angular factor

The chart on `S³` with polar angle `θ` has surface element
`4π sin²(θ) dθ`.  The integral identity below evaluates this chart integral;
the identification of this parameter measure with Mathlib's geometric
surface measure is a separate chart/Jacobian obligation `[需人工审查]`.
-/

open MeasureTheory

namespace JinWishart

noncomputable section

/-- The exponential integral in the usual single-polar-angle chart on `S³`.
This is `4π` times the `sin²` angular integral. -/
def fourDSphereExpAngleIntegralChart (κ : ℝ) : ℝ :=
  4 * Real.pi * ∫ θ in (0 : ℝ)..Real.pi,
    Real.exp (κ * Real.cos θ) * Real.sin θ ^ 2

/-- The `S³` chart angular integral equals `4π² I₁(κ)/κ`. -/
theorem fourDSphereExpAngleIntegralChart_eq_besselI1 (κ : ℝ) (hκ : κ ≠ 0) :
    fourDSphereExpAngleIntegralChart κ =
      4 * Real.pi ^ 2 * besselI1RealSeries κ / κ := by
  rw [fourDSphereExpAngleIntegralChart,
    angularExpSinSqIntegral_eq_pi_besselI1_div κ hκ]
  ring

/-- Multiplying the shifted four-dimensional Gaussian density by its spherical
surface factor and radial Jacobian gives exactly the normalized `(2,1)`
Nuttall radial kernel.  This fixes the coefficient and the `1/a` factor; it
does not itself assert the polar change-of-variables theorem. -/
theorem shiftedGaussianFourDShellFactor_eq_nuttallKernel
    (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    (2 * Real.pi)⁻¹ ^ 2 * r ^ 3 *
        Real.exp (-((r ^ 2 + a ^ 2) / 2)) *
        fourDSphereExpAngleIntegralChart (a * r) =
      noncentralChiFourRadialKernel a r := by
  rw [fourDSphereExpAngleIntegralChart_eq_besselI1 (a * r)
    (mul_ne_zero ha.ne' hr.ne')]
  unfold noncentralChiFourRadialKernel besselI1RealSeries
  field_simp [Real.pi_ne_zero, ha.ne', hr.ne']
  ring

end

end JinWishart
