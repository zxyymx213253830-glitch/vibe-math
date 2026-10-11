import JinWishartFormalization.TwoRowBartlettCoordinateVolume
import Mathlib.Tactic

open JinWishart MeasureTheory ProbabilityTheory
open scoped ENNReal

-- Actual CN normalization pointwise; no assumed density.
theorem deepseek_round3_ComplexScaledDensityNormalize (z : ℂ) :
    ENNReal.ofReal (abs (((Real.sqrt 2)⁻¹) ^ 2)⁻¹) *
        ENNReal.ofReal ((2 * Real.pi)⁻¹ *
          Real.exp (-‖((Real.sqrt 2)⁻¹)⁻¹ • z‖ ^ 2 / 2)) =
      ENNReal.ofReal (Real.pi⁻¹ * Real.exp (-‖z‖ ^ 2)) := by
  sorry
