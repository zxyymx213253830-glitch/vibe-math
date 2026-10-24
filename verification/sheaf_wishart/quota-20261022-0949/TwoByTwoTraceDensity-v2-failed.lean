import JinWishartFormalization.TwoByTwoTraceCoordinates

/-! Codex. Seed2026102405 controls before source.
Actual central Gram trace/traceless density in four real coordinates.
[需人工审查] Exact Lebesgue factor and cone; ordered joint spectral law still separate. -/
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal
namespace JinWishart
noncomputable section

private def traceMeasEquiv : GramChartSpace ≃ᵐ GramChartSpace :=
  twoRowTraceEquiv.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv

theorem twoRowTrace_density_transport (f : GramChartSpace → ℝ≥0∞) (hf : Measurable f) :
    ((volume : Measure GramChartSpace).withDensity f).map twoRowTraceCoordinates =
      volume.withDensity (fun p => 2*f (twoRowTraceInverse p)) := by
  have hmp : MeasurePreserving traceMeasEquiv (volume : Measure GramChartSpace)
      ((2 : ℝ≥0∞) • volume) := by
    refine ⟨traceMeasEquiv.measurable,?_⟩
    change (volume : Measure GramChartSpace).map twoRowTraceEquiv= _
    exact map_volume_twoRowTraceEquiv
  have h := map_withDensity_measurePreserving traceMeasEquiv volume
    ((2 : ℝ≥0∞) • volume) hmp f hf
  rw [withDensity_smul_measure,← withDensity_smul' 2 _ (by norm_num)] at h
  exact h

theorem actualTwoRow_traceCoordinates_eq_density :
    (stdGaussian (ComplexSample (m := 2) (n := 2))).map
      (fun z => twoRowTraceCoordinates (twoRowGramRealCoordinates (complexGram (complexSampleMatrix z)))) =
    (volume.restrict {p : GramChartSpace | 0<p 0 ∧ p 1^2+p 2^2+p 3^2<(p 0)^2}).withDensity
      (fun p => ENNReal.ofReal (2*Real.pi⁻¹*Real.exp (-2*p 0))) := by
  let C : Set GramChartSpace := {q | 0<q 0 ∧ q 1^2+q 2^2<q 0*q 3}
  let D : Set GramChartSpace := {p | 0<p 0 ∧ p 1^2+p 2^2+p 3^2<(p 0)^2}
  have hC : MeasurableSet C := by dsimp [C];measurability
  have hD : MeasurableSet D := by dsimp [D];measurability
  have ht : Measurable twoRowTraceCoordinates := by unfold twoRowTraceCoordinates;fun_prop
  change (stdGaussian (ComplexSample (m := 2) (n := 2))).map
    (twoRowTraceCoordinates ∘ (fun z => twoRowGramRealCoordinates (complexGram (complexSampleMatrix z))))= _
  rw [← Measure.map_map ht (by fun_prop),actualTwoRow_GramRealCoordinates_eq_traceDensity]
  rw [← withDensity_indicator hC, twoRowTrace_density_transport _ (by fun_prop),
    ← withDensity_indicator hD]
  congr 1
  funext p
  have hc : twoRowTraceInverse p ∈ C ↔ p ∈ D := by
    have h := twoRowTraceCoordinates_cone (twoRowTraceInverse p)
    have hi : twoRowTraceCoordinates (twoRowTraceInverse p)=p := twoRowTraceEquiv.apply_symm_apply p
    simpa only [hi] using h
  by_cases hp : p ∈ D
  · rw [Set.indicator_of_mem (hc.mpr hp),Set.indicator_of_mem hp]
    have he : 2*(Real.pi⁻¹*Real.exp (-((twoRowTraceInverse p) 0+(twoRowTraceInverse p) 3)))=
        2*Real.pi⁻¹*Real.exp (-2*p 0) := by
      have hh : (twoRowTraceInverse p) 0+(twoRowTraceInverse p) 3=2*p 0 := by
        simp [twoRowTraceInverse];ring
      rw [hh]
      ring
    rw [← he,ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤2)]
    norm_num
  · rw [Set.indicator_of_notMem (fun h => hp (hc.mp h)),Set.indicator_of_notMem hp,mul_zero]

end
end JinWishart
#print axioms JinWishart.twoRowTrace_density_transport
#print axioms JinWishart.actualTwoRow_traceCoordinates_eq_density
