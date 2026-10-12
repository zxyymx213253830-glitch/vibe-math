import JinWishartFormalization.TwoRowActualNormalizedDensity
import JinWishartFormalization.DeepSeekSpectral20261012.RealTraceTranslation
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

/-- Codex transports the original locally authored real exponential factor
through the coordinate formula and ENNReal coercion. -/
theorem twoRowTraceDensity_translate (p : GramChartSpace) (x : ℝ) :
    twoRowTraceDensity (p + twoRowShiftCoordinates x) =
      ENNReal.ofReal (Real.exp (-2 * x)) * twoRowTraceDensity p := by
  unfold twoRowTraceDensity
  simp only [Pi.add_apply, twoRowShiftCoordinates_zero, twoRowShiftCoordinates_three]
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
  congr 1
  rw [← add_assoc, deepseek_spectral_RealTraceTranslation]
  ring

/-- Exact translated-cone mass from the established actual Gram density.
[需人工审查] Translation of coordinate Lebesgue measure. -/
theorem twoRowShiftedCone_traceMass (x : ℝ) :
    (∫⁻ q in twoRowShiftedCone x, twoRowTraceDensity q) =
      ENNReal.ofReal (Real.exp (-2 * x)) := by
  have hc := (measurePreserving_add_right (volume : Measure GramChartSpace)
      (twoRowShiftCoordinates x)).setLIntegral_comp_emb
    (MeasurableEquiv.addRight (twoRowShiftCoordinates x)).measurableEmbedding
    twoRowTraceDensity twoRowPositiveCone
  calc
    _ = ∫⁻ p in twoRowPositiveCone,
        twoRowTraceDensity (p + twoRowShiftCoordinates x) := by
      rw [twoRowShiftedCone_eq_image]
      exact hc.symm
    _ = ∫⁻ p in twoRowPositiveCone,
        ENNReal.ofReal (Real.exp (-2 * x)) * twoRowTraceDensity p := by
      simp_rw [twoRowTraceDensity_translate]
    _ = ENNReal.ofReal (Real.exp (-2 * x)) *
        (∫⁻ p in twoRowPositiveCone, twoRowTraceDensity p) :=
      lintegral_const_mul _ measurable_twoRowTraceDensity
    _ = _ := by
      have hm : (∫⁻ p in twoRowPositiveCone, twoRowTraceDensity p) = 1 :=
        twoRowGram_traceDensity_mass
      rw [hm, mul_one]

/-- Actual central complex 2x2 Wishart mass of a positive shifted Gram cone.
The threshold/spectrum identification is a separate theorem. -/
theorem actualTwoRow_shiftedCone_probability (x : ℝ) (hx : 0 ≤ x) :
    ((complexWishart (m := 2) (n := 2)).map twoRowGramRealCoordinates)
        (twoRowShiftedCone x) = ENNReal.ofReal (Real.exp (-2 * x)) := by
  rw [complexWishart_twoRow_realCoordinates_eq_traceDensity]
  change ((volume.restrict twoRowPositiveCone).withDensity twoRowTraceDensity)
    (twoRowShiftedCone x) = _
  rw [withDensity_apply _ (measurableSet_twoRowShiftedCone x),
    Measure.restrict_restrict (measurableSet_twoRowShiftedCone x),
    Set.inter_eq_left.mpr (twoRowShiftedCone_subset_positive x hx)]
  exact twoRowShiftedCone_traceMass x

end
end JinWishart

#print axioms JinWishart.twoRowShiftedCone_eq_image
#print axioms JinWishart.twoRowShiftedCone_subset_positive
#print axioms JinWishart.twoRowTraceDensity_translate
#print axioms JinWishart.twoRowShiftedCone_traceMass
#print axioms JinWishart.actualTwoRow_shiftedCone_probability
