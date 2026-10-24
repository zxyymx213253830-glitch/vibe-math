import JinWishartFormalization.TwoByTwoTraceRadiusLaw
import JinWishartFormalization.TwoByTwoSpectralLinearTransport
import JinWishartFormalization.TwoByTwoOrderedEigenpair

/-! Codex. Seeds2026102405/2407/2408 preceded this source.
Actual original-source ordered central2x2 Gram density; no hDensity premise.
[需人工审查] Lebesgue/angular factors, original paper T3 interpretation and model. -/
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace JinWishart
noncomputable section

theorem actualCentralTwoByTwo_jointEigenvalueDensity :
    centralTwoByTwoJointEigenvalueLaw =
      (volume : Measure (ℝ × ℝ)).withDensity centralTwoByTwoPaperEigenvalueDensity := by
  have ht : Measurable twoRowTraceCoordinates := by unfold twoRowTraceCoordinates;fun_prop
  have hr : Measurable twoRowTraceRadius := by unfold twoRowTraceRadius traceVectorCoordinates;fun_prop
  have hA : Measurable actualTwoRowTraceRadius := hr.comp (ht.comp
    (measurable_twoRowGramRealCoordinates.comp measurable_complexSampleGram))
  have he : Measurable traceRadiusEigenCoordinates := by unfold traceRadiusEigenCoordinates;fun_prop
  have hsame : centralTwoByTwoEigenpair=traceRadiusEigenCoordinates ∘ actualTwoRowTraceRadius := by
    funext z
    rw [centralTwoByTwoEigenpair_eq_traceSpectralPair]
    have hv (p : GramChartSpace) : (fun j : Fin 3 => p j.succ)=![p 1,p 2,p 3] := by
      funext j
      fin_cases j <;> rfl
    simp only [Function.comp_def,actualTwoRowTraceRadius,twoRowTraceRadius,
      traceVectorCoordinates,traceRadiusEigenCoordinates,twoRowTraceSpectralPair,hv]
  rw [centralTwoByTwoJointEigenvalueLaw,hsame,← Measure.map_map he hA,
    actualTwoRow_traceRadius_eq_density,traceRadiusDensity_spectral_transport]

theorem actualCentralTwoByTwo_T3Increment_densityIntegral (x : ℝ) :
    centralTwoByTwoT3Increment x =
      ∫⁻ y in centralTwoByTwoT3Region x, centralTwoByTwoPaperEigenvalueDensity y
        ∂(volume : Measure (ℝ × ℝ)) :=
  centralTwoByTwoT3Increment_eq_densityIntegral x actualCentralTwoByTwo_jointEigenvalueDensity

end
end JinWishart
#print axioms JinWishart.actualCentralTwoByTwo_jointEigenvalueDensity
#print axioms JinWishart.actualCentralTwoByTwo_T3Increment_densityIntegral
