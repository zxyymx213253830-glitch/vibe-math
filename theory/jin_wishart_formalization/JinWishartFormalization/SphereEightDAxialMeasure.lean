import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Eight-dimensional axial measure: normalization stage

This file records the exact sphere masses and checks the normalization of the
candidate axial-angle density on `S⁷`.  The full pushforward identity from
`toSphere` to the `sin⁶ θ` chart is not proved here; see the module header in
`EightDimensionalAngularBesselI3.lean` and the execution note returned to the
coordinator for the remaining geometric bridge.
-/

open MeasureTheory Set

namespace JinWishart

noncomputable section

local notation "E₈" => EuclideanSpace ℝ (Fin 8)
local notation "E₇" => EuclideanSpace ℝ (Fin 7)

/-- Total real mass of Mathlib's geometric `toSphere` measure on `S⁷`. -/
theorem sphereEightMeasure_univ_real :
    ((volume : Measure E₈).toSphere).real Set.univ = Real.pi ^ 4 / 3 := by
  rw [Measure.toSphere_real_apply_univ]
  have hdim : Module.finrank ℝ E₈ = 8 := by simp
  rw [hdim]
  change (8 : ℝ) * ENNReal.toReal (volume (Metric.ball (0 : E₈) 1)) = _
  rw [InnerProductSpace.volume_ball_of_dim_even (E := E₈) (k := 4) (by simp) 0 1]
  norm_num [ENNReal.toReal_mul]
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi ^ 4 / 24)]
  ring

/-- Area of `S⁶`, the transverse angular factor in the axial chart on `S⁷`. -/
theorem sphereSevenMeasure_univ_real :
    ((volume : Measure E₇).toSphere).real Set.univ = 16 * Real.pi ^ 3 / 15 := by
  rw [Measure.toSphere_real_apply_univ]
  have hdim : Module.finrank ℝ E₇ = 7 := by simp
  rw [hdim]
  change (7 : ℝ) * ENNReal.toReal (volume (Metric.ball (0 : E₇) 1)) = _
  rw [InnerProductSpace.volume_ball_of_dim_odd (E := E₇) (k := 3) (by simp) 0 1]
  simp only [ENNReal.toReal_mul]
  norm_num [Nat.doubleFactorial]
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi ^ 3 * 16 / 105)]
  ring

/-- Constant-function check for the proposed S⁷ axial-angle density. -/
theorem sphereEight_axial_weight_mass :
    (16 * Real.pi ^ 3 / 15) *
      (∫ θ in (0 : ℝ)..Real.pi, Real.sin θ ^ 6) = Real.pi ^ 4 / 3 := by
  rw [integral_sin_pow]
  norm_num
  rw [integral_sin_pow]
  norm_num <;> ring

end

end JinWishart
