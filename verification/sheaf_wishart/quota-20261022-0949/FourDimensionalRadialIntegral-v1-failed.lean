import JinWishartFormalization.ThreeDimensionalRadialIntegral
import JinWishartFormalization.TwoByTwoTraceCoordinates

/-! Codex. Seed2026102407 controls before source.
Split four real coordinates into a trace and Euclidean R3, then integrate radius.
[需人工审查] Product Lebesgue normalization and nonnegative Tonelli. -/
open MeasureTheory Set
open scoped ENNReal
namespace JinWishart
noncomputable section

def traceVectorCoordinates (p : GramChartSpace) : ℝ × EuclideanSpace ℝ (Fin 3) :=
  (p 0,WithLp.toLp 2 (fun j : Fin 3 => p j.succ))

theorem measurePreserving_traceVectorCoordinates :
    MeasurePreserving traceVectorCoordinates := by
  have h := ((measurePreserving_id (μ := (volume : Measure ℝ))).prod
    (PiLp.volume_preserving_toLp (Fin 3))).comp
    (volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 0)
  change MeasurePreserving (fun p : GramChartSpace =>
    (p 0,WithLp.toLp 2 (fun j : Fin 3 => p ((0 : Fin 4).succAbove j)))) at h
  simpa only [Fin.succAbove_zero] using h

theorem lintegral_trace_radius_fin_four (F : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p : GramChartSpace, F ((traceVectorCoordinates p).1,‖(traceVectorCoordinates p).2‖)) =
      ENNReal.ofReal (4*Real.pi) *
        ∫⁻ t : ℝ, ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r^2)*F (t,r) := by
  have hm : Measurable (fun x : ℝ × EuclideanSpace ℝ (Fin 3) => F (x.1,‖x.2‖)) := by
    fun_prop
  calc
    _ = ∫⁻ x : ℝ × EuclideanSpace ℝ (Fin 3),F (x.1,‖x.2‖) :=
      measurePreserving_traceVectorCoordinates.lintegral_comp hm
    _ = ∫⁻ t : ℝ, ∫⁻ v : EuclideanSpace ℝ (Fin 3), F (t,‖v‖) := by
      exact lintegral_prod _ hm.aemeasurable
    _ = ∫⁻ t : ℝ, ENNReal.ofReal (4*Real.pi) *
        ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r^2)*F (t,r) := by
      apply lintegral_congr
      intro t
      exact lintegral_norm_volume_fin_three (fun r => F (t,r)) (by fun_prop)
    _ = _ := lintegral_const_mul' _ _ (by finiteness)

end
end JinWishart
#print axioms JinWishart.measurePreserving_traceVectorCoordinates
#print axioms JinWishart.lintegral_trace_radius_fin_four
