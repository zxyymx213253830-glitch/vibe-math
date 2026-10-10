import JinWishartFormalization.DeepSeekHour20261010.GammaZeroBoundary
import JinWishartFormalization.TwoRowBartlettSupport
import JinWishartFormalization.TwoRowBartlettSupport
import JinWishartFormalization.TwoRowBartlettSupport
import JinWishartFormalization.TwoRowBartlettSupport
import JinWishartFormalization.DeepSeekCollaboration20261010.ComplexDensityNonnegative
import JinWishartFormalization.TwoRowRandomDirectionLaw
import JinWishartFormalization.GaussianRawCoordinates
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Tactic

open JinWishart MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem deepseek_hour_ComplexDensityMeasurable :
    Measurable (fun z : ℂ => ENNReal.ofReal (Real.pi⁻¹ * Real.exp (-‖z‖ ^ 2))) := by
  apply Measurable.ennreal_ofReal
  -- Use the fact that the function is a composition of measurable functions
  <;> measurability
  <;> simp [Measurable.const, Measurable.id, Measurable.pow, Measurable.norm]
  <;> apply Measurable.const
  <;> simp [Measurable.const, Measurable.id, Measurable.pow, Measurable.norm]
  <;> apply Measurable.const
  <;> simp [Measurable.const, Measurable.id, Measurable.pow, Measurable.norm]
  <;> apply Measurable.const
  <;> simp [Measurable.const, Measurable.id, Measurable.pow, Measurable.norm]
  <;> apply Measurable.const
  <;> simp [Measurable.const, Measurable.id, Measurable.pow, Measurable.norm]
  <;> apply Measurable.const
  <;> simp [Measurable.const, Measurable.id, Measurable.pow, Measurable.norm]
  <;> apply Measurable.const
  <;> simp [Measurable.const, Measurable.id, Measurable.pow, Measurable.norm]
  <;> apply Measurable.const
  <;> simp [Measurable.const, Measurable.id, Measurable.pow, Measurable.norm]
  <;> apply Measurable.const

#print axioms deepseek_hour_ComplexDensityMeasurable
