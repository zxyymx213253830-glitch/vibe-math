import JinWishartFormalization.LogDetErrorBounds
import JinWishartFormalization.FatouIntegralDivergence

/-! Infinite first inverse moment forces divergent scaled logarithmic error.
Codex. [需人工审查] Fatou and finite-real-integral vs infinite nonnegative limit.
-/
open MeasureTheory Filter
open scoped Topology
namespace JinWishart
noncomputable section

theorem scaled_log_inverse_error_tendsto_atTop {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (hf : AEMeasurable f μ)
    (hpos : ∀ᵐ a ∂μ, 0 < f a) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hinv : Integrable (fun a => ((f a)⁻¹)^p) μ)
    (htop : (∫⁻ a, ENNReal.ofReal ((f a)⁻¹) ∂μ) = ⊤) :
    Tendsto (fun r : ℝ => r*(∫ a, Real.log (1+(r*f a)⁻¹) ∂μ)) atTop atTop := by
  have ht : Tendsto (fun r : ℝ => ∫ a, r*Real.log (1+(r*f a)⁻¹) ∂μ) atTop atTop := by
    apply tendsto_integral_atTop_of_ae_limit_lintegral_top μ _ (fun a => (f a)⁻¹) _ _ _ _ htop
    · intro r
      exact (aemeasurable_const.mul (Real.measurable_log.comp_aemeasurable
        (aemeasurable_const.add (aemeasurable_const.mul hf).inv))).aestronglyMeasurable
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
      exact (integrable_log_inverse_error μ f hf hpos r p hr hp hp1 hinv).const_mul r
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
      exact hpos.mono (fun a ha => mul_nonneg hr.le
        (log_inverse_error_bound r (f a) p hr ha hp hp1).1)
    · filter_upwards [hpos] with a ha
      apply (Real.tendsto_mul_log_one_add_div_atTop ((f a)⁻¹)).congr'
      exact Filter.Eventually.of_forall (fun r => by
        change r*Real.log (1+(f a)⁻¹/r)=r*Real.log (1+(r*f a)⁻¹)
        rw [_root_.mul_inv_rev,div_eq_mul_inv])
  simpa only [integral_const_mul] using ht

end
end JinWishart
#print axioms JinWishart.scaled_log_inverse_error_tendsto_atTop
