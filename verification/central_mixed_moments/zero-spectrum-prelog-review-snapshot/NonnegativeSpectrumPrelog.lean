import JinWishartFormalization.FiniteSpectrumLogDetGrowth

/-! Expected high-scale prelog with zero modes and no absolute-log moment.
Codex. L1/nonnegative spectra only. [需人工审查] AE/DCT/integral interpretation.
-/
open MeasureTheory Filter
open scoped Topology
namespace JinWishart
noncomputable section

theorem log_one_add_mul_prelog_nonneg (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun r : ℝ => Real.log (1+r*x)/Real.log r) atTop
      (𝓝 (if 0<x then 1 else 0)) := by
  by_cases hp : 0<x
  · rw [if_pos hp]
    have ha : Tendsto (fun r : ℝ => x+r⁻¹) atTop (𝓝 x) := by
      simpa using (tendsto_const_nhds.add tendsto_inv_atTop_zero :
        Tendsto (fun r : ℝ => x+r⁻¹) atTop (𝓝 (x+0)))
    have hl := (Real.continuousAt_log hp.ne').tendsto.comp ha
    have ht := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).add
      (hl.div_atTop Real.tendsto_log_atTop)
    apply (show Tendsto (fun r : ℝ => 1+Real.log (x+r⁻¹)/Real.log r) atTop (𝓝 1) by
      simpa using ht).congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr
    have hrp : 0<r := lt_trans zero_lt_one hr
    have harg : 0<x+r⁻¹ := by positivity
    have he : 1+r*x=r*(x+r⁻¹) := by field_simp; ring
    rw [he,Real.log_mul hrp.ne' harg.ne']
    field_simp [(Real.log_pos hr).ne']
    <;> ring
  · have hz : x=0 := le_antisymm (le_of_not_gt hp) hx
    simp [hz]

theorem log_one_add_mul_prelog_norm_bound (x r : ℝ) (hx : 0 ≤ x)
    (hr : 1 ≤ r) (hl : 1 ≤ Real.log r) :
    ‖Real.log (1+r*x)/Real.log r‖ ≤ 1+x := by
  have hrp : 0<r := zero_lt_one.trans_le hr
  have hlp : 0<Real.log r := zero_lt_one.trans_le hl
  have h1 : 0<1+x := by positivity
  have h2 : 0<1+r*x := by positivity
  have hb : 1+r*x ≤ r*(1+x) := by nlinarith
  have hu : Real.log (1+r*x) ≤ Real.log r+Real.log (1+x) := by
    calc
      _ ≤ Real.log (r*(1+x)) := Real.log_le_log h2 hb
      _ = _ := Real.log_mul hrp.ne' h1.ne'
  have hxlog := Real.log_le_sub_one_of_pos h1
  have hn : 0 ≤ Real.log (1+r*x) := Real.log_nonneg (by nlinarith)
  rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg hn hlp.le)]
  apply (div_le_iff₀ hlp).mpr
  nlinarith [mul_nonneg hx (sub_nonneg.mpr hl)]

theorem integral_log_one_add_mul_prelog_nonneg {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ) (hf : Integrable f μ)
    (hn : ∀ᵐ a ∂μ, 0 ≤ f a) :
    Tendsto (fun r : ℝ => (∫ a, Real.log (1+r*f a) ∂μ)/Real.log r) atTop
      (𝓝 (∫ a, (if 0<f a then (1 : ℝ) else 0) ∂μ)) := by
  have ht : Tendsto (fun r : ℝ => ∫ a, Real.log (1+r*f a)/Real.log r ∂μ) atTop
      (𝓝 (∫ a, (if 0<f a then (1 : ℝ) else 0) ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun a => 1+f a)
    · exact Eventually.of_forall (fun r =>
        ((Real.measurable_log.comp_aemeasurable
          (aemeasurable_const.add (aemeasurable_const.mul hf.aemeasurable))).div_const
            (Real.log r)).aestronglyMeasurable)
    · filter_upwards [eventually_ge_atTop (max (1 : ℝ) (Real.exp 1))] with r hr
      have hr1 : 1 ≤ r := (le_max_left _ _).trans hr
      have hre : Real.exp 1 ≤ r := (le_max_right _ _).trans hr
      have hl : 1 ≤ Real.log r := by
        calc
          1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
          _ ≤ _ := Real.log_le_log (Real.exp_pos 1) hre
      exact hn.mono (fun a ha => log_one_add_mul_prelog_norm_bound (f a) r ha hr1 hl)
    · exact (integrable_const (1 : ℝ)).add hf
    · exact hn.mono (fun a ha => log_one_add_mul_prelog_nonneg (f a) ha)
  simpa only [integral_div] using ht

theorem integral_finiteSpectrumLogDet_prelog_nonneg {α ι : Type*}
    [MeasurableSpace α] [Fintype ι] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : ι → α → ℝ) (hf : ∀ i, Integrable (f i) μ)
    (hn : ∀ i, ∀ᵐ a ∂μ, 0 ≤ f i a) :
    Tendsto (fun r : ℝ => (∫ a, finiteSpectrumLogDet (fun i => f i a) r ∂μ)/Real.log r)
      atTop (𝓝 (∑ i, ∫ a, (if 0<f i a then (1 : ℝ) else 0) ∂μ)) := by
  classical
  have ht := tendsto_finsetSum Finset.univ (fun i _ =>
    integral_log_one_add_mul_prelog_nonneg μ (f i) (hf i) (hn i))
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  have hrp : 0<r := zero_lt_one.trans_le hr
  rw [show (∫ a, finiteSpectrumLogDet (fun i => f i a) r ∂μ) =
      ∑ i, ∫ a, Real.log (1+r*f i a) ∂μ from
    integral_finsetSum _ (fun i _ => integrable_log_one_add_mul μ (f i) (hf i) (hn i) r hrp.le)]
  exact (Finset.sum_div _ _ _).symm

end
end JinWishart
#print axioms JinWishart.log_one_add_mul_prelog_nonneg
#print axioms JinWishart.log_one_add_mul_prelog_norm_bound
#print axioms JinWishart.integral_log_one_add_mul_prelog_nonneg
#print axioms JinWishart.integral_finiteSpectrumLogDet_prelog_nonneg
