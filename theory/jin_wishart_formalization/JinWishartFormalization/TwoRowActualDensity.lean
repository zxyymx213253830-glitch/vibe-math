import JinWishartFormalization.TwoRowBartlettCoordinateVolume
import JinWishartFormalization.DeepSeekCollaborationRound220261010.ComplexRadialDensityMeasurableGuided
import JinWishartFormalization.DeepSeekCollaborationRound320261011.ComplexScaledCoefficient
import JinWishartFormalization.DeepSeekCollaborationRound320261011.ComplexScaledNormSquare

/-!
# Actual density bridges in the third collaboration hour
Codex authors the probability-law composition and coordinate transport.
The radial ENNReal measurability proof is reused verbatim from local DeepSeek,
with its original GUIDED_COLLABORATION provenance. Existing fixed-seed 200000
actual-model/closed-form controls were checked in prior rounds, not new proofs.
[需人工审查] Measure normalization, dimensions, and interpretation of paper model.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace JinWishart

/-- Actual scaled standard complex Gaussian law; no density hypothesis. -/
theorem stdGaussian_complex_scaled_eq_withDensity (r : ℝ) (hr : r ≠ 0) :
    (stdGaussian ℂ).map (fun z => r • z) =
      (volume : Measure ℂ).withDensity (fun z =>
        ENNReal.ofReal (abs (r ^ 2)⁻¹) *
          ENNReal.ofReal ((2 * Real.pi)⁻¹ * Real.exp (-‖r⁻¹ • z‖ ^ 2 / 2))) := by
  rw [stdGaussian_complex_eq_radialDensity]
  exact map_withDensity_smul_complex r hr _ deepseek_round2_ComplexRadialDensityMeasurable

/-- Exact unnormalized-in-syntax density of the actual CN factor.
It retains the checked scalar Jacobian; no simplifying identity is assumed. -/
noncomputable def twoRowComplexDensityRaw (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (abs (((Real.sqrt 2)⁻¹) ^ 2)⁻¹) *
    ENNReal.ofReal ((2 * Real.pi)⁻¹ *
      Real.exp (-‖((Real.sqrt 2)⁻¹)⁻¹ • z‖ ^ 2 / 2))

theorem measurable_twoRowComplexDensityRaw : Measurable twoRowComplexDensityRaw := by
  unfold twoRowComplexDensityRaw
  fun_prop

noncomputable def twoRowBartlettDensityRaw (p : ℝ × (ℂ × ℝ)) : ℝ≥0∞ :=
  gammaPDF 2 1 p.1 * (twoRowComplexDensityRaw p.2.1 * gammaPDF 1 1 p.2.2)

theorem measurable_twoRowBartlettDensityRaw : Measurable twoRowBartlettDensityRaw := by
  exact ((measurable_gammaDensity_ennreal 2 1).comp measurable_fst).mul
    ((measurable_twoRowComplexDensityRaw.comp (measurable_fst.comp measurable_snd)).mul
      ((measurable_gammaDensity_ennreal 1 1).comp (measurable_snd.comp measurable_snd)))

/-- Actual Bartlett density, retaining the explicit complex scaling formula. -/
theorem actualTwoRow_BartlettCoordinates_eq_withDensity_raw :
    (stdGaussian (ComplexSample (m := 2) (n := 2))).map twoRowBartlettCoordinates =
      (volume : Measure (ℝ × (ℂ × ℝ))).withDensity twoRowBartlettDensityRaw := by
  rw [actualTwoRow_BartlettCoordinates_law,
    stdGaussian_complex_scaled_eq_withDensity (Real.sqrt 2)⁻¹
      (inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (by norm_num))))]
  change ((volume : Measure ℝ).withDensity (gammaPDF 2 1)).prod
    (((volume : Measure ℂ).withDensity twoRowComplexDensityRaw).prod
      ((volume : Measure ℝ).withDensity (gammaPDF 1 1))) = _
  rw [prod_withDensity measurable_twoRowComplexDensityRaw (measurable_gammaDensity_ennreal 1 1)]
  have hinner : Measurable (fun p : ℂ × ℝ =>
      twoRowComplexDensityRaw p.1 * gammaPDF 1 1 p.2) :=
    (measurable_twoRowComplexDensityRaw.comp measurable_fst).mul
      ((measurable_gammaDensity_ennreal 1 1).comp measurable_snd)
  rw [prod_withDensity (measurable_gammaDensity_ennreal 2 1) hinner]
  simp only [← Measure.volume_eq_prod]
  rfl

noncomputable def twoRowBartlettRealDensityRaw (q : GramChartSpace) : ℝ≥0∞ :=
  twoRowBartlettDensityRaw (twoRowBartlettCoordinateEquiv.symm q)

theorem measurable_twoRowBartlettRealDensityRaw : Measurable twoRowBartlettRealDensityRaw :=
  measurable_twoRowBartlettDensityRaw.comp twoRowBartlettCoordinateEquiv.symm.measurable

/-- The actual encoded Bartlett law has density with respect to Fin 4 real volume. -/
theorem actualTwoRow_BartlettRealCoordinates_eq_withDensity_raw :
    (stdGaussian (ComplexSample (m := 2) (n := 2))).map
        (twoRowBartlettRealCoordinates ∘ twoRowBartlettCoordinates) =
      (volume : Measure GramChartSpace).withDensity twoRowBartlettRealDensityRaw := by
  rw [← Measure.map_map measurable_twoRowBartlettRealCoordinates
    measurable_twoRowBartlettCoordinates,
    actualTwoRow_BartlettCoordinates_eq_withDensity_raw,
    twoRowBartlettCoordinate_density_transport _ measurable_twoRowBartlettDensityRaw]
  rfl

noncomputable def twoRowGramDensityRaw (q : GramChartSpace) : ℝ≥0∞ :=
  twoRowBartlettRealDensityRaw (twoRowGramChartInverse q) / ENNReal.ofReal (q 0)

theorem measurable_twoRowGramDensityRaw : Measurable twoRowGramDensityRaw :=
  (measurable_twoRowBartlettRealDensityRaw.comp measurable_twoRowGramChartInverse).div
    ((measurable_pi_apply 0).ennreal_ofReal)

/-- Actual central complex 2x2 Gram density on its positive domain.
No assumed probability density is used. The exact density retains GammaPDF
and the known scalar formula until the local normalization lemmas are checked. -/
theorem actualTwoRow_GramRealCoordinates_eq_withDensity_raw :
    (stdGaussian (ComplexSample (m := 2) (n := 2))).map
      (fun z => twoRowGramRealCoordinates (complexGram (complexSampleMatrix z))) =
      (volume.restrict
        {q : GramChartSpace | 0 < q 0 ∧ q 1 ^ 2 + q 2 ^ 2 < q 0 * q 3}).withDensity
          twoRowGramDensityRaw := by
  have hd : (((gammaMeasure 2 1).prod
      (((stdGaussian ℂ).map (fun z => (Real.sqrt 2)⁻¹ • z)).prod (expMeasure 1))).map
        twoRowBartlettRealCoordinates) =
      (volume : Measure GramChartSpace).withDensity twoRowBartlettRealDensityRaw := by
    rw [← actualTwoRow_BartlettRealCoordinates_law]
    exact actualTwoRow_BartlettRealCoordinates_eq_withDensity_raw
  have hpos := actualTwoRow_BartlettRealLaw_restrict_positive
  rw [hd] at hpos
  have hs : MeasurableSet {p : GramChartSpace | 0 < p 0 ∧ 0 < p 3} :=
    (measurableSet_lt measurable_const (measurable_pi_apply 0)).inter
      (measurableSet_lt measurable_const (measurable_pi_apply 3))
  rw [restrict_withDensity hs] at hpos
  rw [actualTwoRow_GramRealCoordinates_law, hd, ← hpos]
  exact twoRowGramChart_density_map _ measurable_twoRowBartlettRealDensityRaw

/-- Positive-support Gamma(2,1) factor, for simplifying the actual law. -/
theorem twoRow_gamma_two_positive_formula (x : ℝ) (hx : 0 < x) :
    gammaPDF 2 1 x = ENNReal.ofReal (x * Real.exp (-x)) := by
  norm_num [gammaPDF, gammaPDFReal, hx.le]

/-- Positive-support residual factor, for simplifying the actual law. -/
theorem twoRow_gamma_one_positive_formula (x : ℝ) (hx : 0 < x) :
    gammaPDF 1 1 x = ENNReal.ofReal (Real.exp (-x)) := by
  simp [gammaPDF, gammaPDFReal, hx.le, Real.Gamma_one]

/-- Explicit inverse encoding, retaining the coordinate order used by volume. -/
theorem twoRowBartlettCoordinateEquiv_symm_apply (q : GramChartSpace) :
    twoRowBartlettCoordinateEquiv.symm q =
      (q 0, (⟨q 1, q 2⟩, q 3)) := by
  apply twoRowBartlettCoordinateEquiv.injective
  rw [twoRowBartlettCoordinateEquiv.apply_symm_apply,
    twoRowBartlettCoordinateEquiv_apply]
  ext i
  fin_cases i <;> simp [twoRowBartlettRealCoordinates]

/-- Collapse the two real factors on the actual positive Bartlett domain. -/
theorem twoRowBartlettRealDensityRaw_positive_formula (p : GramChartSpace)
    (hs : 0 < p 0) (he : 0 < p 3) :
    twoRowBartlettRealDensityRaw p = ENNReal.ofReal (p 0) *
      (twoRowComplexDensityRaw ⟨p 1, p 2⟩ *
        ENNReal.ofReal (Real.exp (-(p 0 + p 3)))) := by
  unfold twoRowBartlettRealDensityRaw twoRowBartlettDensityRaw
  rw [twoRowBartlettCoordinateEquiv_symm_apply]
  dsimp only
  rw [twoRow_gamma_two_positive_formula _ hs,
    twoRow_gamma_one_positive_formula _ he, ENNReal.ofReal_mul hs.le,
    neg_add, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  ac_rfl

/-- The actual positive Gram chart cancels the first Bartlett energy against
the Jacobian. The complex factor is kept exact until local normalization passes. -/
theorem twoRowGramDensityRaw_positive_formula (q : GramChartSpace)
    (hq : 0 < q 0) (hd : q 1 ^ 2 + q 2 ^ 2 < q 0 * q 3) :
    twoRowGramDensityRaw q =
      twoRowComplexDensityRaw
        ⟨twoRowGramChartInverse q 1, twoRowGramChartInverse q 2⟩ *
      ENNReal.ofReal (Real.exp (-(q 0 + twoRowGramChartInverse q 3))) := by
  have hs : 0 < twoRowGramChartInverse q 0 := by
    simpa [twoRowGramChartInverse] using hq
  unfold twoRowGramDensityRaw
  rw [twoRowBartlettRealDensityRaw_positive_formula _ hs
    (twoRowGramChart_inverse_residual_pos q hq hd)]
  simp only [twoRowGramChartInverse, Matrix.cons_val_zero]
  rw [mul_comm (ENNReal.ofReal (q 0))]
  exact ENNReal.mul_div_cancel_right
    (ne_of_gt (ENNReal.ofReal_pos.mpr hq)) ENNReal.ofReal_ne_top

/-- GUIDED_COLLABORATION: local norm-square result, Codex arithmetic composition.
The local original exponent attempts were not accepted. -/
theorem twoRow_complex_scaled_exponent (z : ℂ) :
    -‖((Real.sqrt 2)⁻¹)⁻¹ • z‖ ^ 2 / 2 = -‖z‖ ^ 2 := by
  rw [inv_inv, deepseek_round3_ComplexScaledNormSquare]
  ring

/-- GUIDED_COLLABORATION: local checked coefficient and norm-square identities;
Codex composes them with the exact ENNReal expression of the actual law. -/
theorem twoRowComplexDensityRaw_normalized (z : ℂ) :
    twoRowComplexDensityRaw z =
      ENNReal.ofReal (Real.pi⁻¹ * Real.exp (-‖z‖ ^ 2)) := by
  unfold twoRowComplexDensityRaw
  rw [twoRow_complex_scaled_exponent]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [← mul_assoc, deepseek_round3_ComplexScaledCoefficient]

/-- Actual central complex 2x2 Gram density equals the trace exponential
on its actual positive domain. This has not been generalized to the paper's
arbitrary dimensions, spectra, or noncentral models. -/
theorem twoRowGramDensityRaw_trace_formula (q : GramChartSpace)
    (hq : 0 < q 0) (hd : q 1 ^ 2 + q 2 ^ 2 < q 0 * q 3) :
    twoRowGramDensityRaw q = ENNReal.ofReal (Real.pi⁻¹ * Real.exp (-(q 0 + q 3))) := by
  rw [twoRowGramDensityRaw_positive_formula q hq hd, twoRowComplexDensityRaw_normalized]
  rw [← ENNReal.ofReal_mul (by positivity), mul_assoc, ← Real.exp_add]
  congr 2
  congr 1
  simp [Complex.sq_norm, Complex.normSq_apply, twoRowGramChartInverse]
  ring

/-- The actual probability law, with the simplified density relative to the
four real coordinates and the exact Gram positive domain. [需人工审查]
Volume convention and identification with the paper remain separate reviews. -/
theorem actualTwoRow_GramRealCoordinates_eq_traceDensity :
    (stdGaussian (ComplexSample (m := 2) (n := 2))).map
      (fun z => twoRowGramRealCoordinates (complexGram (complexSampleMatrix z))) =
      (volume.restrict
        {q : GramChartSpace | 0 < q 0 ∧ q 1 ^ 2 + q 2 ^ 2 < q 0 * q 3}).withDensity
          (fun q => ENNReal.ofReal (Real.pi⁻¹ * Real.exp (-(q 0 + q 3)))) := by
  rw [actualTwoRow_GramRealCoordinates_eq_withDensity_raw]
  apply withDensity_congr_ae
  have hs : MeasurableSet
      {q : GramChartSpace | 0 < q 0 ∧ q 1 ^ 2 + q 2 ^ 2 < q 0 * q 3} := by
    measurability
  filter_upwards [ae_restrict_mem hs] with q hq
  exact twoRowGramDensityRaw_trace_formula q hq.1 hq.2

/-- Exact normalization derived from the actual probability law, not a numerical
integral or an assumed normalization. [需人工审查] Coordinate volume convention. -/
theorem twoRowGram_traceDensity_mass :
    ∫⁻ q in {q : GramChartSpace | 0 < q 0 ∧ q 1 ^ 2 + q 2 ^ 2 < q 0 * q 3},
      ENNReal.ofReal (Real.pi⁻¹ * Real.exp (-(q 0 + q 3))) = 1 := by
  have h := congrArg (fun μ : Measure GramChartSpace => μ Set.univ)
    actualTwoRow_GramRealCoordinates_eq_traceDensity
  have hm : Measurable (fun z : ComplexSample (m := 2) (n := 2) =>
      twoRowGramRealCoordinates (complexGram (complexSampleMatrix z))) :=
    measurable_twoRowGramRealCoordinates.comp
      (measurable_complexSampleGram (m := 2) (n := 2))
  rw [Measure.map_apply hm MeasurableSet.univ] at h
  simpa using h.symm

/-- Actual normalized CN(0,1) factor used by the coordinate-density bridge.
Codex composes the actual scaling law with joint checked normalization. -/
theorem actualTwoRow_Complex_eq_normalizedDensity :
    (stdGaussian ℂ).map (fun z => (Real.sqrt 2)⁻¹ • z) =
      (volume : Measure ℂ).withDensity
        (fun z => ENNReal.ofReal (Real.pi⁻¹ * Real.exp (-‖z‖ ^ 2))) := by
  rw [stdGaussian_complex_scaled_eq_withDensity (Real.sqrt 2)⁻¹
    (inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (by norm_num))))]
  congr 1
  funext z
  exact twoRowComplexDensityRaw_normalized z

end JinWishart

#print axioms JinWishart.stdGaussian_complex_scaled_eq_withDensity
#print axioms JinWishart.measurable_twoRowComplexDensityRaw
#print axioms JinWishart.measurable_twoRowBartlettDensityRaw
#print axioms JinWishart.actualTwoRow_BartlettCoordinates_eq_withDensity_raw

#print axioms JinWishart.measurable_twoRowBartlettRealDensityRaw
#print axioms JinWishart.actualTwoRow_BartlettRealCoordinates_eq_withDensity_raw
#print axioms JinWishart.measurable_twoRowGramDensityRaw
#print axioms JinWishart.actualTwoRow_GramRealCoordinates_eq_withDensity_raw
#print axioms JinWishart.twoRow_gamma_two_positive_formula
#print axioms JinWishart.twoRow_gamma_one_positive_formula
#print axioms JinWishart.twoRowBartlettCoordinateEquiv_symm_apply
#print axioms JinWishart.twoRowBartlettRealDensityRaw_positive_formula
#print axioms JinWishart.twoRowGramDensityRaw_positive_formula
#print axioms JinWishart.twoRow_complex_scaled_exponent
#print axioms JinWishart.twoRowComplexDensityRaw_normalized
#print axioms JinWishart.twoRowGramDensityRaw_trace_formula
#print axioms JinWishart.actualTwoRow_GramRealCoordinates_eq_traceDensity
#print axioms JinWishart.twoRowGram_traceDensity_mass
#print axioms JinWishart.actualTwoRow_Complex_eq_normalizedDensity
