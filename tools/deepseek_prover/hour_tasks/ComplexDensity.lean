import JinWishartFormalization.TwoRowRandomDirectionLaw
import JinWishartFormalization.GaussianRawCoordinates
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Tactic

open JinWishart MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem deepseek_hour_ComplexDensity :
    (stdGaussian ℂ).map (fun z => (Real.sqrt 2)⁻¹ • z) =
    (volume : Measure ℂ).withDensity (fun z => ENNReal.ofReal (Real.pi⁻¹ * Real.exp (-‖z‖ ^ 2))) := by
  sorry
