import JinWishartFormalization.CentralMinimumHardEdgeBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# General central complex Wishart diversity exponent

Codex proofs. The exponent is exact; no sharp leading coefficient is asserted.
[需人工审查] Actual minimum model, right-neighborhood and logarithmic interpretation.
-/
open Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace JinWishart
noncomputable section

theorem tendsto_log_ratio_of_power_bounds (f : ℝ → ℝ) (k : ℕ) (c C : ℝ)
    (hc : 0 < c) (hC : 0 < C)
    (hb : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < x ∧ c*x^k ≤ f x ∧ f x ≤ C*x^k) :
    Tendsto (fun x => Real.log (f x) / Real.log x) (𝓝[>] 0) (𝓝 (k : ℝ)) := by
  have hz : Tendsto (fun x : ℝ => (Real.log x)⁻¹) (𝓝[>] 0) (𝓝 0) :=
    tendsto_inv_atBot_zero.comp Real.tendsto_log_nhdsGT_zero
  have hl : Tendsto (fun x : ℝ => (k : ℝ)+Real.log C / Real.log x) (𝓝[>] 0) (𝓝 (k : ℝ)) := by
    simpa only [div_eq_mul_inv,mul_zero,add_zero] using
      tendsto_const_nhds.add (hz.const_mul (Real.log C))
  have hu : Tendsto (fun x : ℝ => (k : ℝ)+Real.log c / Real.log x) (𝓝[>] 0) (𝓝 (k : ℝ)) := by
    simpa only [div_eq_mul_inv,mul_zero,add_zero] using
      tendsto_const_nhds.add (hz.const_mul (Real.log c))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  · filter_upwards [hb,(eventually_lt_nhds (by norm_num : (0 : ℝ)<1)).filter_mono nhdsWithin_le_nhds]
      with x hx hx1
    have hp : 0 < x^k := pow_pos hx.1 _
    have hf : 0 < f x := (mul_pos hc hp).trans_le hx.2.1
    have hd : Real.log x < 0 := Real.log_neg hx.1 hx1
    have hlog := Real.log_le_log hf hx.2.2
    rw [Real.log_mul hC.ne' hp.ne',Real.log_pow] at hlog
    have h := (div_le_div_of_nonpos_of_le hd.le hlog)
    have hx0 : Real.log x ≠ 0 := hd.ne
    convert h using 1 <;> field_simp <;> ring
  · filter_upwards [hb,(eventually_lt_nhds (by norm_num : (0 : ℝ)<1)).filter_mono nhdsWithin_le_nhds]
      with x hx hx1
    have hp : 0 < x^k := pow_pos hx.1 _
    have hd : Real.log x < 0 := Real.log_neg hx.1 hx1
    have hlog := Real.log_le_log (mul_pos hc hp) hx.2.1
    rw [Real.log_mul hc.ne' hp.ne',Real.log_pow] at hlog
    have h := (div_le_div_of_nonpos_of_le hd.le hlog)
    have hx0 : Real.log x ≠ 0 := hd.ne
    convert h using 1 <;> field_simp <;> ring

theorem actualCentralMinimumCDF_diversity (d n : ℕ) (hn : 0 < n) :
    Tendsto (fun x : ℝ => Real.log (actualCentralMinimumCDF d n x) / Real.log x)
      (𝓝[>] 0) (𝓝 ((d+1 : ℕ) : ℝ)) := by
  apply tendsto_log_ratio_of_power_bounds _ (d+1)
    (Real.exp (-1)/(Nat.factorial (d+1) : ℝ))
    (((n+1 : ℕ) : ℝ)^(d+2)/(Nat.factorial (d+1) : ℝ))
  · positivity
  · positivity
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ)<1)).filter_mono nhdsWithin_le_nhds] with x hx hx1
    exact ⟨hx,actualCentralMinimumCDF_local_power_bounds d n hn x hx hx1.le⟩

end
end JinWishart
#print axioms JinWishart.tendsto_log_ratio_of_power_bounds
#print axioms JinWishart.actualCentralMinimumCDF_diversity
