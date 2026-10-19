import Mathlib.Analysis.Analytic.Order

/-! Generic Taylor ratio limit from vanishing lower derivatives.
Codex deterministic calculus. No positivity/log-exponent assumption is needed. -/
open Filter
open scoped Topology
namespace JinWishart
noncomputable section

theorem analytic_ratio_limit_of_vanishing (f : ℝ → ℝ) (k : ℕ)
    (hf : AnalyticAt ℝ f 0) (hz : ∀ i<k, iteratedDeriv i f 0=0) :
    Tendsto (fun x => f x/x^k) (𝓝[>] 0)
      (𝓝 (iteratedDeriv k f 0/(k.factorial : ℝ))) := by
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

end
end JinWishart
#print axioms JinWishart.analytic_ratio_limit_of_vanishing
