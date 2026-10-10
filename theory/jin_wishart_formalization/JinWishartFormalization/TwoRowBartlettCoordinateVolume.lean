import JinWishartFormalization.TwoRowGramPositive
import JinWishartFormalization.GaussianRadialLaw
import JinWishartFormalization.GaussianRawCoordinates
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Bartlett coordinate volume bridge

Codex direction in the second local DeepSeek collaboration hour.
Reuse existing complex-coordinate volume and finite product equivalences;
do not redo radial integration or assume an actual Bartlett density.
[需人工审查] Volume normalization and correspondence with paper coordinates.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace JinWishart
noncomputable section

def finFourNestedRealEquiv : GramChartSpace ≃ᵐ ℝ × (ℝ × (ℝ × ℝ)) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).trans
    ((MeasurableEquiv.refl ℝ).prodCongr
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
        ((MeasurableEquiv.refl ℝ).prodCongr MeasurableEquiv.finTwoArrow)))

theorem finFourNestedRealEquiv_apply (q : GramChartSpace) :
    finFourNestedRealEquiv q = (q 0, (q 1, (q 2, q 3))) := by
  rfl

def twoRowBartlettCoordinateEquiv : (ℝ × (ℂ × ℝ)) ≃ᵐ GramChartSpace :=
  ((MeasurableEquiv.refl ℝ).prodCongr
    ((Complex.measurableEquivRealProd.prodCongr (MeasurableEquiv.refl ℝ)).trans
      MeasurableEquiv.prodAssoc)).trans finFourNestedRealEquiv.symm

theorem twoRowBartlettCoordinateEquiv_apply (p : ℝ × (ℂ × ℝ)) :
    twoRowBartlettCoordinateEquiv p = twoRowBartlettRealCoordinates p := by
  ext i
  fin_cases i <;> rfl

theorem volume_preserving_finFourNestedRealEquiv :
    MeasurePreserving finFourNestedRealEquiv := by
  have hi : MeasurePreserving (MeasurableEquiv.refl ℝ) := ⟨measurable_id, Measure.map_id⟩
  have h2 := volume_preserving_finTwoArrow ℝ
  have h3 := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  have h4 := volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 0
  exact (hi.prod ((hi.prod h2).comp h3)).comp h4

theorem volume_preserving_twoRowBartlettCoordinateEquiv :
    MeasurePreserving twoRowBartlettCoordinateEquiv := by
  have hi : MeasurePreserving (MeasurableEquiv.refl ℝ) := ⟨measurable_id, Measure.map_id⟩
  have hc := Complex.volume_preserving_equiv_real_prod.prod hi
  have ha := (volume_preserving_prodAssoc (α₁ := ℝ) (β₁ := ℝ) (γ₁ := ℝ)).comp hc
  exact (MeasurePreserving.symm finFourNestedRealEquiv
    volume_preserving_finFourNestedRealEquiv).comp (hi.prod ha)

theorem measurable_twoRowBartlettRealCoordinates : Measurable twoRowBartlettRealCoordinates := by
  have he : (fun p => twoRowBartlettCoordinateEquiv p) = twoRowBartlettRealCoordinates :=
    funext twoRowBartlettCoordinateEquiv_apply
  rw [← he]
  exact twoRowBartlettCoordinateEquiv.measurable

theorem volume_preserving_twoRowBartlettRealCoordinates :
    MeasurePreserving twoRowBartlettRealCoordinates := by
  have he : (fun p => twoRowBartlettCoordinateEquiv p) = twoRowBartlettRealCoordinates :=
    funext twoRowBartlettCoordinateEquiv_apply
  rw [← he]
  exact volume_preserving_twoRowBartlettCoordinateEquiv

/-- Generic density transport; no assertion of an actual Gaussian density. -/
theorem twoRowBartlettCoordinate_density_transport
    (f : ℝ × (ℂ × ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (volume.withDensity f).map twoRowBartlettRealCoordinates =
      volume.withDensity (f ∘ twoRowBartlettCoordinateEquiv.symm) := by
  have he : (fun p => twoRowBartlettCoordinateEquiv p) = twoRowBartlettRealCoordinates :=
    funext twoRowBartlettCoordinateEquiv_apply
  rw [← he]
  exact map_withDensity_measurePreserving twoRowBartlettCoordinateEquiv volume volume
    volume_preserving_twoRowBartlettCoordinateEquiv f hf

/-- Shared interface repair: the real gamma density and ENNReal density differ. -/
theorem measurable_gammaDensity_ennreal (a r : ℝ) : Measurable (gammaPDF a r) := by
  change Measurable (fun x => ENNReal.ofReal (gammaPDFReal a r x))
  exact (measurable_gammaPDFReal a r).ennreal_ofReal

/-- The chart is measurable on the whole coordinate space, including the boundary. -/
theorem measurable_twoRowGramChart : Measurable twoRowGramChart := by
  unfold twoRowGramChart
  fun_prop

theorem measurable_twoRowGramRealCoordinates : Measurable twoRowGramRealCoordinates := by
  unfold twoRowGramRealCoordinates
  fun_prop

/-- Actual Bartlett coordinates in exactly the volume-aligned real encoding. -/
theorem actualTwoRow_BartlettRealCoordinates_law :
    (stdGaussian (ComplexSample (m := 2) (n := 2))).map
      (twoRowBartlettRealCoordinates ∘ twoRowBartlettCoordinates) =
      ((gammaMeasure 2 1).prod
        (((stdGaussian ℂ).map (fun z => (Real.sqrt 2)⁻¹ • z)).prod (expMeasure 1))).map
          twoRowBartlettRealCoordinates := by
  rw [← Measure.map_map measurable_twoRowBartlettRealCoordinates
    measurable_twoRowBartlettCoordinates, actualTwoRow_BartlettCoordinates_law]

/-- The actual Gram law is the real Bartlett law followed by the existing chart.
No density equality is included as a hypothesis. -/
theorem actualTwoRow_GramRealCoordinates_law :
    (stdGaussian (ComplexSample (m := 2) (n := 2))).map
      (fun z => twoRowGramRealCoordinates (complexGram (complexSampleMatrix z))) =
      (((gammaMeasure 2 1).prod
        (((stdGaussian ℂ).map (fun z => (Real.sqrt 2)⁻¹ • z)).prod (expMeasure 1))).map
          twoRowBartlettRealCoordinates).map twoRowGramChart := by
  rw [← actualTwoRow_BartlettRealCoordinates_law,
    Measure.map_map measurable_twoRowGramChart
      (measurable_twoRowBartlettRealCoordinates.comp measurable_twoRowBartlettCoordinates)]
  congr 1
  funext z
  rw [Function.comp_apply, Function.comp_apply, twoRowGramChart_eq_BartlettGram_real,
    actualTwoRow_Gram_eq_BartlettGram]

/-- Complex-coordinate volume interface for a nonzero real scalar. This is
generic density transport, not an assertion of a Gaussian or Bartlett density. -/
theorem map_withDensity_smul_complex (r : ℝ) (hr : r ≠ 0)
    (f : ℂ → ℝ≥0∞) (hf : Measurable f) :
    (volume.withDensity f).map (fun z => r • z) =
      volume.withDensity (fun z => ENNReal.ofReal (abs (r ^ 2)⁻¹) * f (r⁻¹ • z)) := by
  let e : ℂ ≃ᵐ ℂ :=
    (Homeomorph.smul (isUnit_iff_ne_zero.mpr hr).unit).toMeasurableEquiv
  have hmp : MeasurePreserving e volume (volume.map e) := ⟨e.measurable, rfl⟩
  have h := map_withDensity_measurePreserving e volume (volume.map e) hmp f hf
  have he (z : ℂ) : e z = r • z := rfl
  have hes (z : ℂ) : e.symm z = r⁻¹ • z := by
    apply e.injective
    simp only [e.apply_symm_apply, he, smul_smul, mul_inv_cancel₀ hr, one_smul]
  simp only [Function.comp_def, hes] at h
  rw [show (e : ℂ → ℂ) = (fun z => r • z) from funext he] at h
  rw [Measure.map_addHaar_smul volume hr, Complex.finrank_real_complex,
    withDensity_smul_measure] at h
  rw [h]
  exact (withDensity_smul _ (show Measurable (fun z => f (r⁻¹ • z)) from
    hf.comp (by fun_prop))).symm

/-- Nonnegative observables of the actual Gram matrix can be integrated against
the independent actual Bartlett factors, before any density identification. -/
theorem actualTwoRow_GramRealCoordinates_lintegral
    (g : GramChartSpace → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ z, g (twoRowGramRealCoordinates (complexGram (complexSampleMatrix z)))
        ∂stdGaussian (ComplexSample (m := 2) (n := 2)) =
      ∫⁻ p, g (twoRowGramChart (twoRowBartlettRealCoordinates p))
        ∂(gammaMeasure 2 1).prod
          (((stdGaussian ℂ).map (fun z => (Real.sqrt 2)⁻¹ • z)).prod (expMeasure 1)) := by
  have he : (fun z : ComplexSample (m := 2) (n := 2) =>
      twoRowGramRealCoordinates (complexGram (complexSampleMatrix z))) =
      twoRowGramChart ∘ (twoRowBartlettRealCoordinates ∘ twoRowBartlettCoordinates) := by
    funext z
    simp only [Function.comp_apply, twoRowGramChart_eq_BartlettGram_real,
      actualTwoRow_Gram_eq_BartlettGram]
  have hm : Measurable (fun z : ComplexSample (m := 2) (n := 2) =>
      twoRowGramRealCoordinates (complexGram (complexSampleMatrix z))) := by
    rw [he]
    exact measurable_twoRowGramChart.comp
      (measurable_twoRowBartlettRealCoordinates.comp measurable_twoRowBartlettCoordinates)
  rw [← lintegral_map hg hm, actualTwoRow_GramRealCoordinates_law,
    lintegral_map hg measurable_twoRowGramChart]
  exact lintegral_map (hg.comp measurable_twoRowGramChart)
    measurable_twoRowBartlettRealCoordinates

end
end JinWishart

#print axioms JinWishart.volume_preserving_finFourNestedRealEquiv
#print axioms JinWishart.volume_preserving_twoRowBartlettCoordinateEquiv
#print axioms JinWishart.measurable_twoRowBartlettRealCoordinates
#print axioms JinWishart.volume_preserving_twoRowBartlettRealCoordinates
#print axioms JinWishart.twoRowBartlettCoordinate_density_transport
#print axioms JinWishart.measurable_gammaDensity_ennreal
#print axioms JinWishart.measurable_twoRowGramChart
#print axioms JinWishart.measurable_twoRowGramRealCoordinates
#print axioms JinWishart.actualTwoRow_BartlettRealCoordinates_law
#print axioms JinWishart.actualTwoRow_GramRealCoordinates_law
#print axioms JinWishart.map_withDensity_smul_complex
#print axioms JinWishart.actualTwoRow_GramRealCoordinates_lintegral
