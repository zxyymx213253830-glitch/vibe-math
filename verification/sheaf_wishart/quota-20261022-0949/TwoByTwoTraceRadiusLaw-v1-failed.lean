import JinWishartFormalization.TwoByTwoTraceRadiusIntegral

/-! Codex. Prior seeds2026102405/2407 before source.
Actual same-source central 2x2 trace/radius law, from the nonnegative integral identity.
[需人工审查] Measure extensionality, nonnegative Tonelli and strict chamber boundary. -/
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace JinWishart
noncomputable section

def actualTwoRowTraceRadius (z : ComplexSample (m := 2) (n := 2)) : ℝ × ℝ :=
  twoRowTraceRadius (twoRowTraceCoordinates
    (twoRowGramRealCoordinates (complexGram (complexSampleMatrix z))))

theorem actualTwoRow_traceRadius_eq_density :
    (stdGaussian (ComplexSample (m := 2) (n := 2))).map actualTwoRowTraceRadius =
    ((volume : Measure (ℝ × ℝ)).restrict {x | 0<x.2 ∧ x.2<x.1}).withDensity
      (fun x => ENNReal.ofReal (8*x.2^2*Real.exp (-2*x.1))) := by
  let D : Set (ℝ × ℝ) := {x | 0<x.2 ∧ x.2<x.1}
  have hD : MeasurableSet D := by dsimp [D];measurability
  have hw : Measurable (fun x : ℝ × ℝ => ENNReal.ofReal (8*x.2^2*Real.exp (-2*x.1))) := by fun_prop
  have ht : Measurable twoRowTraceCoordinates := by unfold twoRowTraceCoordinates;fun_prop
  have hr : Measurable twoRowTraceRadius := by unfold twoRowTraceRadius traceVectorCoordinates;fun_prop
  have hA : Measurable actualTwoRowTraceRadius := hr.comp (ht.comp
    (measurable_twoRowGramRealCoordinates.comp measurable_complexSampleGram))
  refine Measure.ext_of_lintegral _ fun F hF => ?_
  calc
    _ = ∫⁻ z, F (actualTwoRowTraceRadius z) ∂stdGaussian (ComplexSample (m := 2) (n := 2)) :=
      lintegral_map hF hA
    _ = ∫⁻ t : ℝ, ∫⁻ r in Ioi (0 : ℝ),
        if r<t then ENNReal.ofReal (8*r^2*Real.exp (-2*t))*F (t,r) else 0 := by
      simpa only [actualTwoRowTraceRadius] using actualTwoRow_traceRadius_lintegral F hF
    _ = _ := by
      symm
      rw [lintegral_withDensity_eq_lintegral_mul _ hw hF,← lintegral_indicator hD,
        lintegral_prod _ ((hw.mul hF).indicator hD).aemeasurable]
      apply lintegral_congr
      intro t
      rw [← lintegral_indicator measurableSet_Ioi]
      apply lintegral_congr
      intro r
      by_cases hr0 : 0<r <;> by_cases hrt : r<t <;>
        simp [D,Set.indicator,hr0,hrt]

end
end JinWishart
#print axioms JinWishart.actualTwoRow_traceRadius_eq_density
