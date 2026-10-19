import JinWishartFormalization.AnalyticPositivePowerLimit
import Mathlib.Analysis.Analytic.Order

/-! Sharp positive power coefficient as an ordinary Taylor coefficient.
Codex. No application probability or target coefficient is assumed.
[需人工审查] Interpretation of the derivative formula in actual models. -/
open Filter
open scoped Topology
namespace JinWishart
noncomputable section

theorem analytic_order_of_positive_log_exponent (f : ℝ → ℝ) (k : ℕ)
    (hf : AnalyticAt ℝ f 0) (hp : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0<f x)
    (hl : Tendsto (fun x => Real.log (f x)/Real.log x) (𝓝[>] 0) (𝓝 (k : ℝ))) :
    analyticOrderAt f 0=(k : ℕ∞) := by
  obtain ⟨g,hg,hg0,he⟩ := analytic_positive_factor_of_log_exponent f k hf hp hl
  apply hf.analyticOrderAt_eq_natCast.mpr
  refine ⟨g,hg,hg0.ne',?_⟩
  simpa only [sub_zero,smul_eq_mul] using he

theorem analytic_power_ratio_taylor_limit (f : ℝ → ℝ) (k : ℕ)
    (hf : AnalyticAt ℝ f 0) (hp : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0<f x)
    (hl : Tendsto (fun x => Real.log (f x)/Real.log x) (𝓝[>] 0) (𝓝 (k : ℝ))) :
    Tendsto (fun x => f x/x^k) (𝓝[>] 0)
      (𝓝 (iteratedDeriv k f 0/(k.factorial : ℝ))) := by
  have hz := ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hf).mp
    (analytic_order_of_positive_log_exponent f k hf hp hl)).1
  obtain ⟨F,hF,he⟩ := hf.exists_eventuallyEq_sum_add_pow_mul (k+1)
  have hsum (x : ℝ) :
      (∑ i ∈ Finset.range (k+1), (x^i/(i.factorial : ℝ)) • iteratedDeriv i f 0) =
        (x^k/(k.factorial : ℝ))*iteratedDeriv k f 0 := by
    rw [Finset.sum_range_succ]
    have hs : (∑ i ∈ Finset.range k, (x^i/(i.factorial : ℝ)) • iteratedDeriv i f 0)=0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hz i (Finset.mem_range.mp hi),smul_zero]
    rw [hs,zero_add,smul_eq_mul]
  have hlim : Tendsto (fun x : ℝ => iteratedDeriv k f 0/(k.factorial : ℝ)+x*F x)
      (𝓝[>] 0) (𝓝 (iteratedDeriv k f 0/(k.factorial : ℝ))) := by
    simpa only [zero_mul,add_zero,id_eq] using tendsto_const_nhds.add
      (((show Tendsto (fun x : ℝ => x) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) from tendsto_id).mono_left nhdsWithin_le_nhds).mul
        (hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds))
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin,he.filter_mono nhdsWithin_le_nhds] with x hx heq
  have hx0 : 0<x := hx
  rw [heq,hsum,smul_eq_mul,pow_succ]
  field_simp

theorem analytic_power_taylor_coefficient_pos (f : ℝ → ℝ) (k : ℕ)
    (hf : AnalyticAt ℝ f 0) (hp : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0<f x)
    (hl : Tendsto (fun x => Real.log (f x)/Real.log x) (𝓝[>] 0) (𝓝 (k : ℝ))) :
    0 < iteratedDeriv k f 0/(k.factorial : ℝ) := by
  obtain ⟨a,ha,ht⟩ := analytic_positive_power_ratio_limit f k hf hp hl
  have he := tendsto_nhds_unique ht (analytic_power_ratio_taylor_limit f k hf hp hl)
  rwa [← he]

end
end JinWishart
#print axioms JinWishart.analytic_order_of_positive_log_exponent
#print axioms JinWishart.analytic_power_ratio_taylor_limit
#print axioms JinWishart.analytic_power_taylor_coefficient_pos
