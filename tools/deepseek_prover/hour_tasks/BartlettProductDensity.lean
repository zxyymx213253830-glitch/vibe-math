import JinWishartFormalization.TwoRowRandomDirectionLaw
import JinWishartFormalization.GaussianRawCoordinates
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Tactic

open JinWishart MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem deepseek_hour_BartlettProductDensity :
    (stdGaussian (ComplexSample (m := 2) (n := 2))).map twoRowBartlettCoordinates =
    (volume : Measure (ℝ × (ℂ × ℝ))).withDensity (fun p =>
      gammaPDF 2 1 p.1 * (ENNReal.ofReal (Real.pi⁻¹ * Real.exp (-‖p.2.1‖ ^ 2)) * gammaPDF 1 1 p.2.2)) := by
  sorry
