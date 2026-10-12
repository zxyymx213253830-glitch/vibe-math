import JinWishartFormalization.TwoRowActualNormalizedDensity
import Mathlib.MeasureTheory.Group.LIntegral

/-!
# Actual central complex 2x2 minimum eigenvalue via diagonal translation

Codex proof direction. The actual Gram density has been established separately;
no candidate spectral density is assumed. The fixed-seed actual-model preflight
is recorded in verification/WISHART_TWO_ROW_MINIMUM_TAIL_20261012.json.
[需人工审查] Coordinate volume, variance conventions, spectral-event interpretation.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ComplexOrder

namespace JinWishart
noncomputable section

def twoRowPositiveCone : Set GramChartSpace :=
  {q | 0 < q 0 ∧ q 1 ^ 2 + q 2 ^ 2 < q 0 * q 3}

def twoRowShiftCoordinates (x : ℝ) : GramChartSpace := ![x, 0, 0, x]

@[simp] theorem twoRowShiftCoordinates_zero (x : ℝ) : twoRowShiftCoordinates x 0 = x := rfl
@[simp] theorem twoRowShiftCoordinates_one (x : ℝ) : twoRowShiftCoordinates x 1 = 0 := rfl
@[simp] theorem twoRowShiftCoordinates_two (x : ℝ) : twoRowShiftCoordinates x 2 = 0 := rfl
@[simp] theorem twoRowShiftCoordinates_three (x : ℝ) : twoRowShiftCoordinates x 3 = x := rfl

def twoRowShiftedCone (x : ℝ) : Set GramChartSpace :=
  {q | x < q 0 ∧ q 1 ^ 2 + q 2 ^ 2 < (q 0 - x) * (q 3 - x)}

def twoRowTraceDensity (q : GramChartSpace) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.pi⁻¹ * Real.exp (-(q 0 + q 3)))

theorem measurableSet_twoRowPositiveCone : MeasurableSet twoRowPositiveCone := by
  unfold twoRowPositiveCone
  measurability

theorem measurableSet_twoRowShiftedCone (x : ℝ) : MeasurableSet (twoRowShiftedCone x) := by
  unfold twoRowShiftedCone
  measurability

theorem measurable_twoRowTraceDensity : Measurable twoRowTraceDensity := by
  unfold twoRowTraceDensity
  fun_prop

theorem twoRowShiftedCone_eq_image (x : ℝ) :
    twoRowShiftedCone x =
      (fun p : GramChartSpace => p + twoRowShiftCoordinates x) '' twoRowPositiveCone := by
  ext q
  constructor
  · intro hq
    refine ⟨q - twoRowShiftCoordinates x, ?_, by simp⟩
    change x < q 0 ∧ q 1 ^ 2 + q 2 ^ 2 < (q 0 - x) * (q 3 - x) at hq
    simpa only [twoRowPositiveCone, Set.mem_setOf_eq, Pi.sub_apply,
      twoRowShiftCoordinates_zero, twoRowShiftCoordinates_one,
      twoRowShiftCoordinates_two, twoRowShiftCoordinates_three,
      sub_zero, sub_pos] using hq
  · rintro ⟨p, hp, rfl⟩
    change 0 < p 0 ∧ p 1 ^ 2 + p 2 ^ 2 < p 0 * p 3 at hp
    simpa only [twoRowShiftedCone, Set.mem_setOf_eq, Pi.add_apply,
      twoRowShiftCoordinates_zero, twoRowShiftCoordinates_one,
      twoRowShiftCoordinates_two, twoRowShiftCoordinates_three,
      add_zero, add_sub_cancel_right, lt_add_iff_pos_left] using hp

theorem twoRowShiftedCone_subset_positive (x : ℝ) (hx : 0 ≤ x) :
    twoRowShiftedCone x ⊆ twoRowPositiveCone := by
  rw [twoRowShiftedCone_eq_image]
  rintro q ⟨p, hp, rfl⟩
  change 0 < p 0 ∧ p 1 ^ 2 + p 2 ^ 2 < p 0 * p 3 at hp
  have hp3 : 0 < p 3 := (mul_pos_iff_of_pos_left hp.1).mp
    (lt_of_le_of_lt (add_nonneg (sq_nonneg _) (sq_nonneg _)) hp.2)
  change 0 < (p + twoRowShiftCoordinates x) 0 ∧
    (p + twoRowShiftCoordinates x) 1 ^ 2 +
      (p + twoRowShiftCoordinates x) 2 ^ 2 <
      (p + twoRowShiftCoordinates x) 0 * (p + twoRowShiftCoordinates x) 3
  simp only [Pi.add_apply, twoRowShiftCoordinates_zero, twoRowShiftCoordinates_one,
    twoRowShiftCoordinates_two, twoRowShiftCoordinates_three, add_zero]
  constructor
  · linarith
  · nlinarith [mul_nonneg hx hp.1.le, mul_nonneg hx hp3.le, sq_nonneg x]

end
end JinWishart

#print axioms JinWishart.twoRowShiftedCone_eq_image
#print axioms JinWishart.twoRowShiftedCone_subset_positive
