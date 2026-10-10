import JinWishartFormalization.GaussianRawCoordinates
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Tactic

open JinWishart MeasureTheory ProbabilityTheory
open scoped ENNReal

-- Local-author task template; the hole is never accepted as a proof.
theorem deepseek_round2_ComplexGaussianScaledDensity (r : ℝ) (hr : r ≠ 0) :
    (stdGaussian ℂ).map (fun z => r • z) =
      (volume : Measure ℂ).withDensity (fun z =>
        ENNReal.ofReal (abs (r ^ 2)⁻¹) *
          ENNReal.ofReal ((2 * Real.pi)⁻¹ * Real.exp (-‖r⁻¹ • z‖ ^ 2 / 2))) := by
  sorry
