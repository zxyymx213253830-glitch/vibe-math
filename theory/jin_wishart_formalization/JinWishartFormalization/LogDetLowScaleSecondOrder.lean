import JinWishartFormalization.LogDetLowScale
import Mathlib.Analysis.Calculus.LHopital

/-! Actual second-order expectation limit from a finite nonnegative spectrum.
Codex. No rank, inverse moment or target density assumption.
[需人工审查] Dominated convergence and interpretation of the finite moments.
-/
open MeasureTheory Filter
open scoped Topology
namespace JinWishart
noncomputable section

theorem log_one_add_linear_gap_bounds (u : ℝ) (hu : 0 ≤ u) :
    0 ≤ u-Real.log (1+u) ∧ u-Real.log (1+u) ≤ u^2 := by
  have hp : 0 < 1+u := by positivity
  have hl := Real.log_le_sub_one_of_pos hp
  have hh := Real.one_sub_inv_le_log_of_pos hp
  have he : 1-(1+u)⁻¹ = u/(1+u) := by field_simp; ring
  rw [he] at hh
  refine ⟨by linarith,?_⟩
  calc
    u-Real.log (1+u) ≤ u-u/(1+u) := sub_le_sub_left hh u
    _ = u^2/(1+u) := by field_simp; ring
    _ ≤ u^2 := div_le_self (sq_nonneg u) (by linarith)

theorem log_one_add_second_order_limit (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun r : ℝ => (r*x-Real.log (1+r*x))/r^2) (𝓝[>] 0) (𝓝 (x^2/2)) := by
  have hd : ∀ᶠ r in 𝓝[>] (0 : ℝ),
      HasDerivAt (fun t : ℝ => t*x-Real.log (1+t*x)) (x-x/(1+r*x)) r := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hp : 0 < 1+r*x := by have : 0 < r := hr; positivity
    simpa only [one_mul,id_eq,Pi.sub_apply] using! ((hasDerivAt_id r).mul_const x).sub
      ((((hasDerivAt_id r).mul_const x).const_add 1).log hp.ne')
  have hg : ∀ᶠ r in 𝓝[>] (0 : ℝ), HasDerivAt (fun t : ℝ => t^2) (2*r) r :=
    Eventually.of_forall (fun r => by
      simpa using! (hasDerivAt_id r).fun_pow 2)
  have hgn : ∀ᶠ r in 𝓝[>] (0 : ℝ), 2*r ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have : 0 < r := hr
    positivity
  have hc : ContinuousAt (fun r : ℝ => r*x-Real.log (1+r*x)) 0 := by fun_prop (disch := norm_num)
  have hfa : Tendsto (fun r : ℝ => r*x-Real.log (1+r*x)) (𝓝[>] 0) (𝓝 0) := by
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hga : Tendsto (fun r : ℝ => r^2) (𝓝[>] 0) (𝓝 0) := by
    have hc2 : ContinuousAt (fun r : ℝ => r^2) 0 := by fun_prop
    simpa using hc2.tendsto.mono_left nhdsWithin_le_nhds
  have hq : Tendsto (fun r : ℝ => (x-x/(1+r*x))/(2*r)) (𝓝[>] 0) (𝓝 (x^2/2)) := by
    have hcq : ContinuousAt (fun r : ℝ => x^2/(2*(1+r*x))) 0 := by fun_prop (disch := norm_num)
    apply (show Tendsto (fun r : ℝ => x^2/(2*(1+r*x))) (𝓝[>] 0) (𝓝 (x^2/2)) by
      simpa using hcq.tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hrp : 0 < r := hr
    have hp : 0 < 1+r*x := by positivity
    field_simp
    <;> ring
  exact HasDerivAt.lhopital_zero_nhdsGT hd hg hgn hfa hga hq

theorem integral_log_one_add_second_order {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (hf : Integrable f μ)
    (hf2 : Integrable (fun a => (f a)^2) μ) (hn : ∀ᵐ a ∂μ, 0 ≤ f a) :
    Tendsto (fun r : ℝ => (r*(∫ a, f a ∂μ)-(∫ a, Real.log (1+r*f a) ∂μ))/r^2)
      (𝓝[>] 0) (𝓝 ((∫ a, (f a)^2 ∂μ)/2)) := by
  have ht : Tendsto (fun r : ℝ => ∫ a, (r*f a-Real.log (1+r*f a))/r^2 ∂μ)
      (𝓝[>] 0) (𝓝 (∫ a, (f a)^2/2 ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun a => (f a)^2)
    · exact Eventually.of_forall (fun r =>
        ((hf.aemeasurable.const_mul r).sub (Real.measurable_log.comp_aemeasurable
          (aemeasurable_const.add (aemeasurable_const.mul hf.aemeasurable)))).div_const (r^2)
          |>.aestronglyMeasurable)
    · filter_upwards [self_mem_nhdsWithin] with r hr
      have hrp : 0 < r := hr
      filter_upwards [hn] with a ha
      obtain ⟨h0,h1⟩ := log_one_add_linear_gap_bounds (r*f a) (mul_nonneg hrp.le ha)
      rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg h0 (sq_nonneg r))]
      apply (div_le_iff₀ (sq_pos_of_pos hrp)).mpr
      nlinarith [h1]
    · exact hf2
    · exact hn.mono (fun a ha => log_one_add_second_order_limit (f a) ha)
  rw [integral_div] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hrp : 0 < r := hr
  rw [integral_div,integral_sub (hf.const_mul r)
    (integrable_log_one_add_mul μ f hf hn r hrp.le),integral_const_mul]

theorem integral_finiteSpectrumLogDet_second_order {α ι : Type*}
    [MeasurableSpace α] [Fintype ι] (μ : Measure α) (f : ι → α → ℝ)
    (hf : ∀ i, Integrable (f i) μ) (hf2 : ∀ i, Integrable (fun a => (f i a)^2) μ)
    (hn : ∀ i, ∀ᵐ a ∂μ, 0 ≤ f i a) :
    Tendsto (fun r : ℝ => (r*(∑ i, ∫ a, f i a ∂μ)-
      (∫ a, finiteSpectrumLogDet (fun i => f i a) r ∂μ))/r^2)
      (𝓝[>] 0) (𝓝 ((∑ i, ∫ a, (f i a)^2 ∂μ)/2)) := by
  classical
  have ht := tendsto_finsetSum Finset.univ (fun i _ =>
    integral_log_one_add_second_order μ (f i) (hf i) (hf2 i) (hn i))
  simp only [← Finset.sum_div] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hrp : 0 < r := hr
  rw [show (∫ a, finiteSpectrumLogDet (fun i => f i a) r ∂μ) =
      ∑ i, ∫ a, Real.log (1+r*f i a) ∂μ from
    integral_finsetSum _ (fun i _ => integrable_log_one_add_mul μ (f i) (hf i) (hn i) r hrp.le)]
  simp only [← Finset.sum_div,Finset.sum_sub_distrib,← Finset.mul_sum]

end
end JinWishart
#print axioms JinWishart.log_one_add_linear_gap_bounds
#print axioms JinWishart.log_one_add_second_order_limit
#print axioms JinWishart.integral_log_one_add_second_order
#print axioms JinWishart.integral_finiteSpectrumLogDet_second_order
