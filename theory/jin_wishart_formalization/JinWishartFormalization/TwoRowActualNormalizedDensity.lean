import JinWishartFormalization.TwoRowActualDensity

/-!
# Explicit four-real-coordinate actual Bartlett density

Codex composes the actual probability law, the checked real-coordinate volume
and joint normalization. Local original coefficient/norm-square helpers remain
in TwoRowActualDensity with GUIDED_COLLABORATION provenance.
[需人工审查] Volume convention, coordinate order and paper-model interpretation.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace JinWishart

/-- Explicit positive-domain formula, matching (S,Re Z,Im Z,E) coordinate order. -/
theorem twoRowBartlettRealDensityRaw_normalized_positive (p : GramChartSpace)
    (hs : 0 < p 0) (he : 0 < p 3) :
    twoRowBartlettRealDensityRaw p =
      ENNReal.ofReal (p 0 * Real.pi⁻¹ *
        Real.exp (-(p 0 + p 1 ^ 2 + p 2 ^ 2 + p 3))) := by
  rw [twoRowBartlettRealDensityRaw_positive_formula p hs he,
    twoRowComplexDensityRaw_normalized,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hs.le]
  congr 1
  have heq : Real.exp (-‖(⟨p 1, p 2⟩ : ℂ)‖ ^ 2) *
      Real.exp (-(p 0 + p 3)) =
      Real.exp (-(p 0 + p 1 ^ 2 + p 2 ^ 2 + p 3)) := by
    rw [← Real.exp_add]
    congr 1
    simp [Complex.sq_norm, Complex.normSq_apply]
    ring
  calc
    p 0 * ((Real.pi⁻¹ * Real.exp (-‖(⟨p 1, p 2⟩ : ℂ)‖ ^ 2)) *
        Real.exp (-(p 0 + p 3))) =
        (p 0 * Real.pi⁻¹) * (Real.exp (-‖(⟨p 1, p 2⟩ : ℂ)‖ ^ 2) *
          Real.exp (-(p 0 + p 3))) := by ring
    _ = _ := by rw [heq]

/-- Actual four-real Bartlett law, with no density hypothesis or assumed
normalization; the positive domain follows from the actual law. -/
theorem actualTwoRow_BartlettRealCoordinates_eq_normalizedDensity :
    (stdGaussian (ComplexSample (m := 2) (n := 2))).map
        (twoRowBartlettRealCoordinates ∘ twoRowBartlettCoordinates) =
      (volume.restrict {p : GramChartSpace | 0 < p 0 ∧ 0 < p 3}).withDensity
        (fun p => ENNReal.ofReal (p 0 * Real.pi⁻¹ *
          Real.exp (-(p 0 + p 1 ^ 2 + p 2 ^ 2 + p 3)))) := by
  have hr := actualTwoRow_BartlettRealLaw_restrict_positive
  rw [← actualTwoRow_BartlettRealCoordinates_law,
    actualTwoRow_BartlettRealCoordinates_eq_withDensity_raw] at hr
  have hs : MeasurableSet {p : GramChartSpace | 0 < p 0 ∧ 0 < p 3} :=
    (measurableSet_lt measurable_const (measurable_pi_apply 0)).inter
      (measurableSet_lt measurable_const (measurable_pi_apply 3))
  rw [restrict_withDensity hs] at hr
  rw [actualTwoRow_BartlettRealCoordinates_eq_withDensity_raw, ← hr]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem hs] with p hp
  exact twoRowBartlettRealDensityRaw_normalized_positive p hp.1 hp.2

/-- Exact exponent bridge for the pending actual complex-to-real density.
Codex supplies this after local attempts33-35 did not use the square-norm lemma;
it is an algebra helper, not an independently local density result. -/
theorem twoRow_complex_real_norm_square (p : ℝ × ℝ) :
    ‖Complex.measurableEquivRealProd.symm p‖ ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.measurableEquivRealProd_symm_apply]
  ring

/-- The actual normalized circular complex Gaussian in its two real coordinates.
Codex completes the measure-preserving transport after local attempts36-38
failed; local normalization helpers used upstream keep their original authorship.
[需人工审查] Complex volume convention and variance convention. -/
theorem actualTwoRow_ComplexReal_eq_normalizedDensity :
    ((stdGaussian ℂ).map (fun z => (Real.sqrt 2)⁻¹ • z)).map
        Complex.measurableEquivRealProd =
      (volume : Measure (ℝ × ℝ)).withDensity
        (fun p => ENNReal.ofReal
          (Real.pi⁻¹ * Real.exp (-(p.1 ^ 2 + p.2 ^ 2)))) := by
  rw [actualTwoRow_Complex_eq_normalizedDensity]
  have hf : Measurable (fun z : ℂ =>
      ENNReal.ofReal (Real.pi⁻¹ * Real.exp (-‖z‖ ^ 2))) := by fun_prop
  rw [map_withDensity_measurePreserving Complex.measurableEquivRealProd
    volume volume Complex.volume_preserving_equiv_real_prod _ hf]
  congr 1
  funext p
  simp only [Function.comp_apply, twoRow_complex_real_norm_square]

/-- Expose the checked central complex 2x2 density through the existing Wishart
probability-law API. This is an interface theorem, not a general spectral result.
[需人工审查] Paper convention and coordinate order. -/
theorem complexWishart_twoRow_realCoordinates_eq_traceDensity :
    (complexWishart (m := 2) (n := 2)).map twoRowGramRealCoordinates =
      (volume.restrict {q : GramChartSpace |
        0 < q 0 ∧ q 1 ^ 2 + q 2 ^ 2 < q 0 * q 3}).withDensity
        (fun q => ENNReal.ofReal
          (Real.pi⁻¹ * Real.exp (-(q 0 + q 3)))) := by
  rw [complexWishart, Measure.map_map measurable_twoRowGramRealCoordinates
    measurable_complexSampleGram]
  exact actualTwoRow_GramRealCoordinates_eq_traceDensity

/-- Normalization derived from the actual CN real-coordinate probability law.
Codex completes this interface after two local attempts failed; no independent
local density or radial-integral result is claimed. [需人工审查] Volume convention. -/
theorem twoRow_complexReal_normalizedDensity_mass :
    (∫⁻ p : ℝ × ℝ, ENNReal.ofReal
      (Real.pi⁻¹ * Real.exp (-(p.1 ^ 2 + p.2 ^ 2)))) = 1 := by
  have h := congrArg (fun μ : Measure (ℝ × ℝ) => μ Set.univ)
    actualTwoRow_ComplexReal_eq_normalizedDensity
  simpa using h.symm

end JinWishart

#print axioms JinWishart.twoRowBartlettRealDensityRaw_normalized_positive
#print axioms JinWishart.actualTwoRow_BartlettRealCoordinates_eq_normalizedDensity
#print axioms JinWishart.twoRow_complex_real_norm_square
#print axioms JinWishart.actualTwoRow_ComplexReal_eq_normalizedDensity
#print axioms JinWishart.complexWishart_twoRow_realCoordinates_eq_traceDensity
#print axioms JinWishart.twoRow_complexReal_normalizedDensity_mass
