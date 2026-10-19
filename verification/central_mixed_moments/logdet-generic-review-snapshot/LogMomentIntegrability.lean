import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Logarithmic moments from any positive inverse moment, and log-shift continuity.
Codex. [需人工审查] AE hypotheses and dominated-convergence interpretation.+-/
open MeasureTheory Filter
open scoped Topology
namespace JinWishart
noncomputable section

theorem integrable_log_of_integrable_inverse_rpow {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (hf : Integrable f μ)
    (hfpos : ∀ᵐ a ∂μ, 0 < f a) (p : ℝ) (hp : 0 < p)
    (hinv : Integrable (fun a => ((f a)⁻¹)^p) μ) :
    Integrable (fun a => Real.log (f a)) μ := by
  apply (hf.add (hinv.div_const p)).mono'
    (Real.measurable_log.comp_aemeasurable hf.aemeasurable).aestronglyMeasurable
  filter_upwards [hfpos] with a ha
  change ‖Real.log (f a)‖ ≤ f a+((f a)⁻¹)^p/p
  rw [Real.norm_eq_abs]
  have hpow : 0 ≤ ((f a)⁻¹)^p/p := div_nonneg (Real.rpow_nonneg (by positivity) _) hp.le
  have hu := Real.log_le_sub_one_of_pos ha
  have hl := Real.log_le_rpow_div (inv_nonneg.mpr ha.le) hp
  rw [Real.log_inv] at hl
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem integrable_log_one_add_mul {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (hf : Integrable f μ)
    (hfnonneg : ∀ᵐ a ∂μ, 0 ≤ f a) (r : ℝ) (hr : 0 ≤ r) :
    Integrable (fun a => Real.log (1+r*f a)) μ := by
  apply (hf.const_mul r).mono'
    (Real.measurable_log.comp_aemeasurable
      (aemeasurable_const.add (aemeasurable_const.mul hf.aemeasurable))).aestronglyMeasurable
  filter_upwards [hfnonneg] with a ha
  change ‖Real.log (1+r*f a)‖ ≤ r*f a
  have hpos : 0 < 1+r*f a := by positivity
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg (by nlinarith))]
  have h := Real.log_le_sub_one_of_pos hpos
  linarith

theorem integral_log_add_inverse_tendsto {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (hf : Integrable f μ)
    (hfpos : ∀ᵐ a ∂μ, 0 < f a) (hlog : Integrable (fun a => Real.log (f a)) μ) :
    Tendsto (fun r : ℝ => ∫ a, Real.log (f a+r⁻¹) ∂μ) atTop
      (𝓝 (∫ a, Real.log (f a) ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun a => |Real.log (f a)|+f a)
  · exact Filter.Eventually.of_forall (fun r =>
      (Real.measurable_log.comp_aemeasurable (hf.aemeasurable.add_const _)).aestronglyMeasurable)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    filter_upwards [hfpos] with a ha
    have hrp : 0 < r := lt_of_lt_of_le zero_lt_one hr
    have hi : r⁻¹ ≤ 1 := by
      simpa using one_div_le_one_div_of_le zero_lt_one hr
    have hpos : 0 < f a+r⁻¹ := by positivity
    have hl := Real.log_le_log ha (le_add_of_nonneg_right (inv_nonneg.mpr hrp.le))
    have hu := (Real.log_le_sub_one_of_pos hpos)
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by have := neg_abs_le (Real.log (f a)); linarith,
      by have := le_abs_self (Real.log (f a)); have := abs_nonneg (Real.log (f a)); linarith⟩
  · exact hlog.abs.add hf
  · filter_upwards [hfpos] with a ha
    have ht : Tendsto (fun r : ℝ => f a+r⁻¹) atTop (𝓝 (f a)) := by
      simpa using (tendsto_const_nhds.add tendsto_inv_atTop_zero :
        Tendsto (fun r : ℝ => f a+r⁻¹) atTop (𝓝 (f a+0)))
    exact (Real.continuousAt_log ha.ne').tendsto.comp ht

end
end JinWishart
#print axioms JinWishart.integrable_log_of_integrable_inverse_rpow
#print axioms JinWishart.integrable_log_one_add_mul
#print axioms JinWishart.integral_log_add_inverse_tendsto
