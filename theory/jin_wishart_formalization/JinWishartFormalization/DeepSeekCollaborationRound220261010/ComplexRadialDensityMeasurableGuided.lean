import JinWishartFormalization.GaussianRadialLaw
import Mathlib.Tactic

open MeasureTheory
open scoped ENNReal

-- Remaining measurability subgoal of the actual scalar-law bridge.
theorem deepseek_round2_ComplexRadialDensityMeasurable :
    Measurable (fun z : ℂ =>
      ENNReal.ofReal ((2 * Real.pi)⁻¹ * Real.exp (-‖z‖ ^ 2 / 2))) := by
  apply Measurable.ennreal_ofReal
  -- Use the fact that the composition of measurable functions is measurable
  <;> measurability
  <;> simp_all [Measurable.const]
  <;> apply Measurable.const
  <;> apply Measurable.const
  <;> apply Measurable.const
  <;> apply Measurable.const

#print axioms deepseek_round2_ComplexRadialDensityMeasurable
