import JinWishartFormalization.LogMomentIntegrability
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-! Quantitative log-error bounds and inverse-first-moment correction.
Codex. [需人工审查] AE domination and expectation/limit interchange.
-/
open MeasureTheory Filter
open scoped Topology
namespace JinWishart
noncomputable section

theorem log_one_add_le_rpow_div (u p : ℝ) (hu : 0 ≤ u) (hp : 0 < p) (hp1 : p ≤ 1) :
    Real.log (1+u) ≤ u^p/p := by
  have hpos : 0 < 1+u := by positivity
  have hl := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hpos p)
  rw [Real.log_rpow hpos] at hl
  have hpow := Real.rpow_add_le_add_rpow (show (0 : ℝ) ≤ 1 by norm_num) hu hp.le hp1
  rw [Real.one_rpow] at hpow
  apply (le_div_iff₀ hp).mpr
  nlinarith

theorem log_inverse_error_bound (r x p : ℝ) (hr : 0 < r) (hx : 0 < x)
    (hp : 0 < p) (hp1 : p ≤ 1) :
    0 ≤ Real.log (1+(r*x)⁻¹) ∧
      Real.log (1+(r*x)⁻¹) ≤ (r^p)⁻¹/p*(x⁻¹)^p := by
  constructor
  · exact Real.log_nonneg (by have := inv_nonneg.mpr (mul_nonneg hr.le hx.le); linarith)
  · have h := log_one_add_le_rpow_div ((r*x)⁻¹) p (by positivity) hp hp1
    rw [_root_.mul_inv_rev,Real.mul_rpow (inv_nonneg.mpr hx.le) (inv_nonneg.mpr hr.le),
      Real.inv_rpow hr.le] at h
    convert h using 1 <;> ring

theorem integrable_log_inverse_error {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (hf : AEMeasurable f μ)
    (hpos : ∀ᵐ a ∂μ, 0 < f a) (r p : ℝ) (hr : 0 < r) (hp : 0 < p) (hp1 : p ≤ 1)
    (hinv : Integrable (fun a => ((f a)⁻¹)^p) μ) :
    Integrable (fun a => Real.log (1+(r*f a)⁻¹)) μ := by
  apply (hinv.const_mul ((r^p)⁻¹/p)).mono'
    (Real.measurable_log.comp_aemeasurable
      (aemeasurable_const.add (aemeasurable_const.mul hf).inv)).aestronglyMeasurable
  filter_upwards [hpos] with a ha
  change ‖Real.log (1+(r*f a)⁻¹)‖ ≤ (r^p)⁻¹/p*((f a)⁻¹)^p
  rw [Real.norm_eq_abs,abs_of_nonneg (log_inverse_error_bound r (f a) p hr ha hp hp1).1]
  exact (log_inverse_error_bound r (f a) p hr ha hp hp1).2

theorem integral_log_inverse_error_bounds {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (hf : AEMeasurable f μ)
    (hpos : ∀ᵐ a ∂μ, 0 < f a) (r p : ℝ) (hr : 0 < r) (hp : 0 < p) (hp1 : p ≤ 1)
    (hinv : Integrable (fun a => ((f a)⁻¹)^p) μ) :
    0 ≤ (∫ a, Real.log (1+(r*f a)⁻¹) ∂μ) ∧
      (∫ a, Real.log (1+(r*f a)⁻¹) ∂μ) ≤ (r^p)⁻¹/p*(∫ a, ((f a)⁻¹)^p ∂μ) := by
  have hi := integrable_log_inverse_error μ f hf hpos r p hr hp hp1 hinv
  constructor
  · exact integral_nonneg_of_ae (hpos.mono (fun a ha =>
      (log_inverse_error_bound r (f a) p hr ha hp hp1).1))
  · calc
      _ ≤ ∫ a, (r^p)⁻¹/p*((f a)⁻¹)^p ∂μ :=
        integral_mono_ae hi (hinv.const_mul _) (hpos.mono (fun a ha =>
          (log_inverse_error_bound r (f a) p hr ha hp hp1).2))
      _ = _ := integral_const_mul _ _

theorem integral_log_inverse_error_first_order {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (hf : AEMeasurable f μ)
    (hpos : ∀ᵐ a ∂μ, 0 < f a) (hinv : Integrable (fun a => (f a)⁻¹) μ) :
    Tendsto (fun r : ℝ => r*(∫ a, Real.log (1+(r*f a)⁻¹) ∂μ)) atTop
      (𝓝 (∫ a, (f a)⁻¹ ∂μ)) := by
  have ht : Tendsto (fun r : ℝ => ∫ a, r*Real.log (1+(r*f a)⁻¹) ∂μ) atTop
      (𝓝 (∫ a, (f a)⁻¹ ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun a => (f a)⁻¹)
    · exact Filter.Eventually.of_forall (fun r =>
        (aemeasurable_const.mul (Real.measurable_log.comp_aemeasurable
          (aemeasurable_const.add (aemeasurable_const.mul hf).inv))).aestronglyMeasurable)
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
      filter_upwards [hpos] with a ha
      have h := log_inverse_error_bound r (f a) 1 hr ha (by norm_num) (by norm_num)
      simp only [Real.rpow_one,div_one] at h
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hr.le h.1)]
      have hm := mul_le_mul_of_nonneg_left h.2 hr.le
      simpa only [← mul_assoc,mul_inv_cancel₀ hr.ne',one_mul] using hm
    · exact hinv
    · filter_upwards [hpos] with a ha
      have h := Real.tendsto_mul_log_one_add_div_atTop ((f a)⁻¹)
      apply h.congr'
      exact Filter.Eventually.of_forall (fun r => by
        change r*Real.log (1+(f a)⁻¹/r)=r*Real.log (1+(r*f a)⁻¹)
        rw [_root_.mul_inv_rev,div_eq_mul_inv])
  simpa only [integral_const_mul] using ht

end
end JinWishart
#print axioms JinWishart.log_one_add_le_rpow_div
#print axioms JinWishart.log_inverse_error_bound
#print axioms JinWishart.integrable_log_inverse_error
#print axioms JinWishart.integral_log_inverse_error_bounds
#print axioms JinWishart.integral_log_inverse_error_first_order
