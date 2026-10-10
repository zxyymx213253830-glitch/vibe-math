import JinWishartFormalization.TwoRowRandomDirectionLaw
import JinWishartFormalization.GaussianRawCoordinates
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Tactic

open JinWishart MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem deepseek_hour_GammaTwoPDF :
    ∀ s : ℝ, gammaPDF 2 1 s = ENNReal.ofReal (if 0 ≤ s then s * Real.exp (-s) else 0) := by
  sorry
