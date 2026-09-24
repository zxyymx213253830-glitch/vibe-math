import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The scalar Gaussian-Q layer used by the SER formulas

This defines the standard Gaussian tail directly as an improper integral.  It
does not assume a pre-existing `erfc`/`Q` API, and keeps the normalization
proof connected to mathlib's Gaussian integral theorem.
-/

open MeasureTheory Set

namespace JinWishart

/-- Standard normal density on the real line. -/
noncomputable def standardNormalDensity (x : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2)

/-- Gaussian Q-function, defined as the standard normal upper-tail integral. -/
noncomputable def gaussianQ (x : ℝ) : ℝ :=
  ∫ t in Ioi x, standardNormalDensity t

/-- The standard Gaussian has half its mass on the positive half-line. -/
theorem gaussianQ_zero : gaussianQ 0 = 1 / 2 := by
  unfold gaussianQ standardNormalDensity
  rw [integral_const_mul]
  rw [show (∫ t in Ioi (0 : ℝ), Real.exp (-(t ^ 2) / 2)) =
      Real.sqrt (Real.pi / (1 / 2 : ℝ)) / 2 by
        simpa [div_eq_mul_inv, mul_comm] using (integral_gaussian_Ioi (1 / 2 : ℝ))]
  field_simp [Real.sqrt_ne_zero'.mpr (by positivity : 0 < 2 * Real.pi)]

end JinWishart
