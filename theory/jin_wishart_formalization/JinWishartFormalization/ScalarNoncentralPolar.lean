import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import JinWishartFormalization.BesselI0Angle

/-!
# Polar-coordinate reduction for a shifted planar Gaussian kernel

This file isolates the geometric polar-coordinate step in the scalar
noncentral Wishart calculation and evaluates the angle for a real center.  It
does not yet handle a general complex center or identify the translated-ball
mass with a Nuttall-Q tail.
-/

open MeasureTheory Set

namespace JinWishart

/-- The squared distance from a polar point to a real center, expanded into
the cosine form used by the Rice/Nuttall-Q angular integral. -/
theorem polarPoint_sub_real_norm_sq (r θ c : ℝ) :
    ‖(r : ℂ) * (Real.cos θ + Real.sin θ * Complex.I) - (c : ℂ)‖ ^ 2 =
      r ^ 2 + c ^ 2 - 2 * r * c * Real.cos θ := by
  rw [RCLike.norm_sq_eq_def]
  simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.cos_ofReal_re,
    Complex.sin_ofReal_re]
  calc
    _ = r ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) + c ^ 2 -
        2 * r * c * Real.cos θ := by ring
    _ = _ := by rw [Real.cos_sq_add_sin_sq]; ring

/-- The exponential-cosine angular integral is independent of the chosen
full-period interval.  Mathlib's periodic interval-integral theorem applies
directly, so no improper-integral or endpoint assumptions are needed. -/
theorem angularExpIntegral_negPi_pi_eq_zero_twoPi (a : ℝ) :
    (∫ θ in (-Real.pi)..Real.pi, Real.exp (a * Real.cos θ)) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.exp (a * Real.cos θ) := by
  have hperiodic : Function.Periodic
      (fun θ : ℝ => Real.exp (a * Real.cos θ)) (2 * Real.pi) := by
    intro θ
    simp [Real.cos_add_two_pi]
  have h := hperiodic.intervalIntegral_add_eq (-Real.pi) 0
  convert h using 1 <;> congr 1 <;> ring

/-- The angular part of the real-centered polar Gaussian is exactly the
order-zero modified Bessel factor. -/
theorem polarGaussian_angularIntegral_eq_besselI0 (r c : ℝ) :
    (((∫ θ in (-Real.pi)..Real.pi,
      Real.exp (-(‖(r : ℂ) * (Real.cos θ + Real.sin θ * Complex.I) -
        (c : ℂ)‖ ^ 2) / 2)) : ℝ) : ℂ) =
      (2 * Real.pi : ℂ) *
        (Real.exp (-((r ^ 2 + c ^ 2) / 2)) : ℂ) *
          modifiedBesselI 0 ((r * c : ℝ) : ℂ) := by
  have hpoint (θ : ℝ) :
      Real.exp (-(‖(r : ℂ) * (Real.cos θ + Real.sin θ * Complex.I) -
          (c : ℂ)‖ ^ 2) / 2) =
        Real.exp (-((r ^ 2 + c ^ 2) / 2)) *
          Real.exp (r * c * Real.cos θ) := by
    rw [polarPoint_sub_real_norm_sq]
    rw [show -(r ^ 2 + c ^ 2 - 2 * r * c * Real.cos θ) / 2 =
      -((r ^ 2 + c ^ 2) / 2) + r * c * Real.cos θ by ring]
    rw [Real.exp_add]
  have hInt :
      (∫ θ in (-Real.pi)..Real.pi,
        Real.exp (-(‖(r : ℂ) * (Real.cos θ + Real.sin θ * Complex.I) -
          (c : ℂ)‖ ^ 2) / 2)) =
        Real.exp (-((r ^ 2 + c ^ 2) / 2)) *
          ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.exp (r * c * Real.cos θ) := by
    calc
      _ = ∫ θ in (-Real.pi)..Real.pi,
          Real.exp (-((r ^ 2 + c ^ 2) / 2)) *
            Real.exp (r * c * Real.cos θ) := by
              apply intervalIntegral.integral_congr
              intro θ hθ
              exact hpoint θ
      _ = Real.exp (-((r ^ 2 + c ^ 2) / 2)) *
          ∫ θ in (-Real.pi)..Real.pi, Real.exp (r * c * Real.cos θ) := by
            rw [intervalIntegral.integral_const_mul]
      _ = _ := by rw [angularExpIntegral_negPi_pi_eq_zero_twoPi]
  rw [hInt, Complex.ofReal_mul, angularExpIntegral_eq_modifiedBesselI_zero]
  push_cast
  ring

/-- A shifted Gaussian kernel integrated over a disk centered at the origin,
written as an integral over Mathlib's polar-coordinate chart.  This is the
basic change-of-variables step needed before applying the order-zero Bessel
angular-average identity. -/
theorem integral_shiftedGaussian_closedBall_eq_polar
    (μ : ℂ) (R : ℝ) :
    (∫ z in Metric.closedBall (0 : ℂ) R,
      Real.exp (-(‖z - μ‖ ^ 2) / 2)) =
      ∫ p in Complex.polarCoord.target,
        p.1 * (if p.1 ≤ R then
          Real.exp (-(‖Complex.polarCoord.symm p - μ‖ ^ 2) / 2) else 0) := by
  rw [← MeasureTheory.integral_indicator measurableSet_closedBall]
  rw [← Complex.integral_comp_polarCoord_symm]
  apply setIntegral_congr_fun Complex.polarCoord.open_target.measurableSet
  intro p hp
  change p ∈ Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi at hp
  have hp0 : 0 < p.1 := hp.1
  simp [Set.indicator, Metric.mem_closedBall, dist_eq_norm, abs_of_pos hp0]

end JinWishart
