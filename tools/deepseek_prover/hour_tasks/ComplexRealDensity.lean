import JinWishartFormalization.TwoRowRandomDirectionLaw
import JinWishartFormalization.GaussianRawCoordinates
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Tactic

open JinWishart MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem deepseek_hour_ComplexRealDensity :
    ((stdGaussian ℂ).map (fun z => (Real.sqrt 2)⁻¹ • z)).map Complex.measurableEquivRealProd =
    (volume : Measure (ℝ × ℝ)).withDensity (fun p => ENNReal.ofReal (Real.pi⁻¹ * Real.exp (-(p.1 ^ 2 + p.2 ^ 2)))) := by
  sorry
