import JinWishartFormalization.CentralMinimumDiversity
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Positive analytic germs: a logarithmic power exponent gives a sharp ratio limit

Only an analytic continuation is required; a piecewise CDF itself need not be
analytic across zero. Codex. [需人工审查] Asymptotic interpretation in applications.
-/
open Filter
open scoped Topology
namespace JinWishart
noncomputable section

theorem analytic_positive_factor_of_log_exponent (f : ℝ → ℝ) (k : ℕ)
    (hf : AnalyticAt ℝ f 0) (hp : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0<f x)
    (hl : Tendsto (fun x => Real.log (f x)/Real.log x) (𝓝[>] 0) (𝓝 (k : ℝ))) :
    ∃ g : ℝ → ℝ, AnalyticAt ℝ g 0 ∧ 0<g 0 ∧
      ∀ᶠ x in 𝓝 (0 : ℝ), f x=x^k*g x := by
  have hnot : ¬∀ᶠ x in 𝓝 (0 : ℝ), f x=0 := by
    intro hz
    have hfalse : ∀ᶠ x in 𝓝[>] (0 : ℝ), False := by
      filter_upwards [hp,hz.filter_mono nhdsWithin_le_nhds] with x hx hzero
      exact (ne_of_gt hx) hzero
    obtain ⟨x,hx⟩ := Filter.Eventually.exists hfalse
    exact hx
  obtain ⟨j,g,hg,hg0,hfg⟩ := hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnot
  have hgf : ∀ᶠ x in 𝓝[>] (0 : ℝ), f x=x^j*g x := by
    filter_upwards [hfg.filter_mono nhdsWithin_le_nhds] with x hx
    simpa only [sub_zero,smul_eq_mul] using hx
  have hgp : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0<g x := by
    filter_upwards [self_mem_nhdsWithin,hp,hgf] with x hx hpx he
    rw [he] at hpx
    exact (mul_pos_iff_of_pos_left (pow_pos hx j)).mp hpx
  have hg0p : 0<g 0 := lt_of_le_of_ne
    (ge_of_tendsto (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) (hgp.mono fun _ h => h.le))
    (Ne.symm hg0)
  have hbounds : ∀ᶠ x in 𝓝[>] (0 : ℝ),
      0<x ∧ (g 0/2)*x^j≤f x ∧ f x≤(2*g 0)*x^j := by
    have hlo := hg.continuousAt.eventually (eventually_gt_nhds (show g 0/2<g 0 by linarith))
    have hup := hg.continuousAt.eventually (eventually_lt_nhds (show g 0<2*g 0 by linarith))
    filter_upwards [self_mem_nhdsWithin,hgf,hlo.filter_mono nhdsWithin_le_nhds,
      hup.filter_mono nhdsWithin_le_nhds] with x hx he hxl hxu
    refine ⟨hx,?_,?_⟩ <;> rw [he]
    · nlinarith [mul_le_mul_of_nonneg_right hxl.le (pow_nonneg hx.le j)]
    · nlinarith [mul_le_mul_of_nonneg_right hxu.le (pow_nonneg hx.le j)]
  have hj := tendsto_log_ratio_of_power_bounds f j (g 0/2) (2*g 0)
    (by positivity) (by positivity) hbounds
  have heq : j=k := Nat.cast_injective (tendsto_nhds_unique hj hl)
  subst j
  refine ⟨g,hg,hg0p,?_⟩
  filter_upwards [hfg] with x hx
  simpa only [sub_zero,smul_eq_mul] using hx

theorem analytic_positive_power_ratio_limit (f : ℝ → ℝ) (k : ℕ)
    (hf : AnalyticAt ℝ f 0) (hp : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0<f x)
    (hl : Tendsto (fun x => Real.log (f x)/Real.log x) (𝓝[>] 0) (𝓝 (k : ℝ))) :
    ∃ a : ℝ, 0<a ∧ Tendsto (fun x => f x/x^k) (𝓝[>] 0) (𝓝 a) := by
  obtain ⟨g,hg,hg0,he⟩ := analytic_positive_factor_of_log_exponent f k hf hp hl
  refine ⟨g 0,hg0,?_⟩
  apply (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin,he.filter_mono nhdsWithin_le_nhds] with x hx hxe
  have hx0 : 0<x := hx
  rw [hxe]
  exact (mul_div_cancel_left₀ _ (pow_ne_zero _ hx0.ne')).symm

end
end JinWishart
#print axioms JinWishart.analytic_positive_factor_of_log_exponent
#print axioms JinWishart.analytic_positive_power_ratio_limit
