import JinWishartFormalization.FourDimensionalRadialIntegral
import JinWishartFormalization.TwoByTwoTraceDensity

/-! Codex candidate. Prior seeds2026102405/2407 calibrated actual central2x2
joint/radial and product-volume reductions before this source.
[需人工审查] Original-source pushforward, nonnegative Tonelli and normalization. -/
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace JinWishart
noncomputable section

def twoRowTraceRadius (p : GramChartSpace) : ℝ × ℝ :=
  ((traceVectorCoordinates p).1,‖(traceVectorCoordinates p).2‖)

private theorem traceRadius_cone (p : GramChartSpace) :
    (0<p 0 ∧ p 1^2+p 2^2+p 3^2<(p 0)^2) ↔ (twoRowTraceRadius p).2<p 0 := by
  have hv : (fun j : Fin 3 => p j.succ)=![p 1,p 2,p 3] := by
    funext j
    fin_cases j <;> rfl
  simpa only [twoRowTraceRadius,traceVectorCoordinates,hv] using twoRowTraceCone_iff_norm p

theorem actualTwoRow_traceRadius_lintegral (F : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z : ComplexSample (m := 2) (n := 2),
      F (twoRowTraceRadius (twoRowTraceCoordinates
        (twoRowGramRealCoordinates (complexGram (complexSampleMatrix z))))) ∂stdGaussian _) =
    ∫⁻ t : ℝ, ∫⁻ r in Ioi (0 : ℝ),
      if r<t then ENNReal.ofReal (8*r^2*Real.exp (-2*t))*F (t,r) else 0 := by
  let D : Set GramChartSpace := {p | 0<p 0 ∧ p 1^2+p 2^2+p 3^2<(p 0)^2}
  let T := fun z : ComplexSample (m := 2) (n := 2) => twoRowTraceCoordinates
    (twoRowGramRealCoordinates (complexGram (complexSampleMatrix z)))
  let K : ℝ × ℝ → ℝ≥0∞ := fun x =>
    if x.2<x.1 then ENNReal.ofReal (2*Real.pi⁻¹*Real.exp (-2*x.1))*F x else 0
  have hD : MeasurableSet D := by dsimp [D];measurability
  have ht : Measurable twoRowTraceCoordinates := by unfold twoRowTraceCoordinates;fun_prop
  have hT : Measurable T := ht.comp
    (measurable_twoRowGramRealCoordinates.comp measurable_complexSampleGram)
  have hR : Measurable twoRowTraceRadius := by unfold twoRowTraceRadius traceVectorCoordinates;fun_prop
  have hK : Measurable K :=
    Measurable.ite (measurableSet_lt measurable_snd measurable_fst) (by fun_prop) measurable_const
  have hFR : Measurable (fun p : GramChartSpace => F (twoRowTraceRadius p)) := hF.comp hR
  have hmp : MeasurePreserving T (stdGaussian (ComplexSample (m := 2) (n := 2)))
      ((volume.restrict D).withDensity (fun p => ENNReal.ofReal (2*Real.pi⁻¹*Real.exp (-2*p 0)))) :=
    ⟨hT,actualTwoRow_traceCoordinates_eq_density⟩
  calc
    _ = ∫⁻ p, F (twoRowTraceRadius p)
        ∂(volume.restrict D).withDensity (fun p => ENNReal.ofReal (2*Real.pi⁻¹*Real.exp (-2*p 0))) :=
      hmp.lintegral_comp (hF.comp hR)
    _ = ∫⁻ p : GramChartSpace,K (twoRowTraceRadius p) := by
      rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hFR,← lintegral_indicator hD]
      apply lintegral_congr
      intro p
      by_cases hp : p ∈ D
      · rw [Set.indicator_of_mem hp]
        change ENNReal.ofReal (2*Real.pi⁻¹*Real.exp (-2*p 0))*F (twoRowTraceRadius p)=
          if (twoRowTraceRadius p).2<p 0 then
            ENNReal.ofReal (2*Real.pi⁻¹*Real.exp (-2*p 0))*F (twoRowTraceRadius p) else 0
        rw [if_pos ((traceRadius_cone p).mp hp)]
      · rw [Set.indicator_of_notMem hp]
        change 0=if (twoRowTraceRadius p).2<p 0 then
          ENNReal.ofReal (2*Real.pi⁻¹*Real.exp (-2*p 0))*F (twoRowTraceRadius p) else 0
        rw [if_neg (fun h => hp ((traceRadius_cone p).mpr h))]
    _ = ENNReal.ofReal (4*Real.pi) *
        ∫⁻ t : ℝ, ∫⁻ r in Ioi (0 : ℝ),ENNReal.ofReal (r^2)*K (t,r) :=
      lintegral_trace_radius_fin_four K hK
    _ = _ := by
      rw [← lintegral_const_mul' _ _ (by finiteness)]
      apply lintegral_congr
      intro t
      rw [← lintegral_const_mul' _ _ (by finiteness)]
      apply lintegral_congr
      intro r
      by_cases hrt : r<t
      · simp only [K,hrt,if_pos]
        have he : (4*Real.pi*r^2)*(2*Real.pi⁻¹*Real.exp (-2*t))=
            8*r^2*Real.exp (-2*t) := by field_simp;ring
        rw [← mul_assoc,← mul_assoc,← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity),he]
      · simp [K,hrt]

end
end JinWishart
#print axioms JinWishart.actualTwoRow_traceRadius_lintegral
