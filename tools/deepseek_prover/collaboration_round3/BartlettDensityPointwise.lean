import JinWishartFormalization.TwoRowActualDensity
import Mathlib.Tactic

open JinWishart MeasureTheory ProbabilityTheory
open scoped ENNReal

-- Density-factor identity only; actual probability transport is a separate theorem.
theorem deepseek_round3_BartlettDensityPointwise (p : ℝ × (ℂ × ℝ)) :
    twoRowBartlettDensityRaw p = gammaPDF 2 1 p.1 *
      (ENNReal.ofReal (Real.pi⁻¹ * Real.exp (-‖p.2.1‖ ^ 2)) * gammaPDF 1 1 p.2.2) := by
  sorry
