import JinWishartFormalization.TwoRowHermitianThreshold
import JinWishartFormalization.TwoRowSmallestEigenvalueCDF

/-!
# Actual central complex 2x2 minimum-eigenvalue tail and CDF

Codex composes the actual Gram density, diagonal translation, and the Hermitian
threshold criterion. The previously checked real exponential factor retains its
local DeepSeek GUIDED_COLLABORATION authorship. No spectral density is assumed.
[需人工审查] Volume, unit complex variance, and paper-model conventions.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ComplexOrder

namespace JinWishart
noncomputable section

def twoRowActualMinimum (z : ComplexSample (m := 2) (n := 2)) : ℝ :=
  complexNoncentralSampleSmallestEigenvalue (0 : Matrix (Fin 2) (Fin 2) ℂ)
    (by norm_num) z

theorem measurable_twoRowActualMinimum : Measurable twoRowActualMinimum :=
  measurable_complexNoncentralSampleSmallestEigenvalue _ _

theorem hermitian_twoRow_shiftedCone_iff_smallest
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.IsHermitian) (x : ℝ) :
    twoRowGramRealCoordinates A ∈ twoRowShiftedCone x ↔ x < hA.eigenvalues₀ 1 := by
  let B := A - (x : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
  have hI : ((x : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).IsHermitian := by
    simp [smul_one_eq_diagonal, Matrix.isHermitian_diagonal_iff, isSelfAdjoint_iff]
  have hB : B.IsHermitian := hA.sub hI
  have h0 : (B 0 0).re = (A 0 0).re - x := by simp [B, Matrix.smul_apply]
  have h3 : (B 1 1).re = (A 1 1).re - x := by simp [B, Matrix.smul_apply]
  have h1 : (B 0 1).re = (A 0 1).re := by simp [B, Matrix.smul_apply]
  have h2 : (B 0 1).im = (A 0 1).im := by simp [B, Matrix.smul_apply]
  have he : twoRowGramRealCoordinates A ∈ twoRowShiftedCone x ↔ B.PosDef := by
    change (x < (A 0 0).re ∧ (A 0 1).re ^ 2 + (A 0 1).im ^ 2 <
      ((A 0 0).re - x) * ((A 1 1).re - x)) ↔ B.PosDef
    rw [hermitian_twoRow_posDef_iff B hB, hermitian_twoRow_det_re B hB,
      h0, h3, h1, h2]
    constructor
    · rintro ⟨ha, hd⟩
      refine ⟨sub_pos.mpr ha, ?_⟩
      linarith only [hd]
    · rintro ⟨ha, hd⟩
      refine ⟨sub_pos.mp ha, ?_⟩
      linarith only [hd]
  exact he.trans (hermitian_twoRow_shift_posDef_iff_smallest A hA x)

theorem twoRowActualMinimum_threshold_event
    (z : ComplexSample (m := 2) (n := 2)) (x : ℝ) :
    twoRowGramRealCoordinates (complexSampleGram z) ∈ twoRowShiftedCone x ↔
      x < twoRowActualMinimum z := by
  have hi : smallestEigenvalue₀Index (n := 2) (by norm_num) =
      (1 : Fin (Fintype.card (Fin 2))) := by
    apply Fin.ext
    simp [smallestEigenvalue₀Index]
  have h := hermitian_twoRow_shiftedCone_iff_smallest
    (complexGram (complexSampleMatrix z))
    (complexGram_posSemidef (complexSampleMatrix z)).1 x
  simpa only [twoRowActualMinimum, complexNoncentralSampleSmallestEigenvalue,
    add_zero, hi, complexSampleGram] using h

/-- True minimum-eigenvalue survival probability, derived from the actual Gram law.
[需人工审查] Spectral threshold identification and probability-model conventions. -/
theorem actualTwoRow_minimum_tail (x : ℝ) (hx : 0 ≤ x) :
    (stdGaussian (ComplexSample (m := 2) (n := 2)))
      {z | x < twoRowActualMinimum z} = ENNReal.ofReal (Real.exp (-2 * x)) := by
  have h := actualTwoRow_shiftedCone_probability x hx
  rw [complexWishart,
    Measure.map_map measurable_twoRowGramRealCoordinates measurable_complexSampleGram,
    Measure.map_apply
      (measurable_twoRowGramRealCoordinates.comp measurable_complexSampleGram)
      (measurableSet_twoRowShiftedCone x)] at h
  have he : (twoRowGramRealCoordinates ∘ complexSampleGram) ⁻¹' twoRowShiftedCone x =
      {z | x < twoRowActualMinimum z} := by
    ext z
    exact twoRowActualMinimum_threshold_event z x
  rw [he] at h
  exact h

/-- CDF on every nonnegative threshold, with no assumed eigenvalue density. -/
theorem actualTwoRow_minimum_CDF (x : ℝ) (hx : 0 ≤ x) :
    ((stdGaussian (ComplexSample (m := 2) (n := 2)))
      {z | twoRowActualMinimum z ≤ x}).toReal = 1 - Real.exp (-2 * x) := by
  have hs : MeasurableSet {z | x < twoRowActualMinimum z} :=
    measurableSet_lt measurable_const measurable_twoRowActualMinimum
  have hc := probReal_add_probReal_compl
    (μ := stdGaussian (ComplexSample (m := 2) (n := 2))) hs
  have he : {z | x < twoRowActualMinimum z}ᶜ = {z | twoRowActualMinimum z ≤ x} := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
  rw [he] at hc
  simp only [Measure.real] at hc
  rw [actualTwoRow_minimum_tail x hx, ENNReal.toReal_ofReal (Real.exp_nonneg _)] at hc
  linarith only [hc]

theorem twoRowActualMinimum_nonneg (z : ComplexSample (m := 2) (n := 2)) :
    0 ≤ twoRowActualMinimum z :=
  complexNoncentralGram_eigenvalues₀_nonneg _ _ _

/-- The CDF as a Stieltjes function, including all negative thresholds. -/
theorem actualTwoRow_minimum_cdf_function (x : ℝ) :
    cdf ((stdGaussian (ComplexSample (m := 2) (n := 2))).map twoRowActualMinimum) x =
      if 0 ≤ x then 1 - Real.exp (-2 * x) else 0 := by
  rw [cdf_eq_real, Measure.real,
    Measure.map_apply measurable_twoRowActualMinimum measurableSet_Iic]
  change ((stdGaussian (ComplexSample (m := 2) (n := 2)))
    {z | twoRowActualMinimum z ≤ x}).toReal = _
  by_cases hx : 0 ≤ x
  · rw [if_pos hx]
    exact actualTwoRow_minimum_CDF x hx
  · rw [if_neg hx]
    have he : {z : ComplexSample (m := 2) (n := 2) |
        twoRowActualMinimum z ≤ x} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact not_le_of_gt (lt_of_lt_of_le (lt_of_not_ge hx) (twoRowActualMinimum_nonneg z)) hz
    simp [he]

/-- Identify the actual minimum law as Exp(rate 2), using CDF uniqueness.
[需人工审查] Unit complex variance and exponential rate convention. -/
theorem actualTwoRow_minimum_law_expTwo :
    (stdGaussian (ComplexSample (m := 2) (n := 2))).map twoRowActualMinimum =
      expMeasure 2 := by
  have : IsProbabilityMeasure (expMeasure 2) :=
    isProbabilityMeasure_expMeasure (by norm_num)
  apply Measure.eq_of_cdf
  apply StieltjesFunction.ext
  intro x
  rw [actualTwoRow_minimum_cdf_function, cdf_expMeasure_eq (by norm_num : (0 : ℝ) < 2)]
  simp only [neg_mul]

end
end JinWishart

#print axioms JinWishart.hermitian_twoRow_shiftedCone_iff_smallest
#print axioms JinWishart.twoRowActualMinimum_threshold_event
#print axioms JinWishart.actualTwoRow_minimum_tail
#print axioms JinWishart.actualTwoRow_minimum_CDF
#print axioms JinWishart.actualTwoRow_minimum_cdf_function
#print axioms JinWishart.actualTwoRow_minimum_law_expTwo
