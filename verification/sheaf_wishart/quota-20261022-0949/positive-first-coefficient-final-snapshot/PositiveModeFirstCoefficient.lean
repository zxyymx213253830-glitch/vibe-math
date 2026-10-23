import JinWishartFormalization.FiniteSpectrumOffsetInverseRate
import JinWishartFormalization.NoiselessRowFirstCorrection

/-! First high-scale coefficient for a single nonnegative mode, with zero
mode handled explicitly. Codex. Controls seed2026102242:731 checks before source.
[需人工审查] Subsequent dominated convergence and positive-spectrum meaning. -/
open Filter
open scoped Topology
namespace JinWishart
noncomputable section

theorem positiveModeOffsetError_scaled_tendsto (x : ℝ) (hx : 0≤x) :
    Tendsto (fun t : ℝ => t*positiveModeOffsetError x t) atTop (𝓝 x⁻¹) := by
  by_cases hp : 0<x
  · have he (t : ℝ) (ht : 0<t) :
        positiveModeOffsetError x t=Real.log (1+(t*x)⁻¹) := by
      have htx : t*x≠0 := mul_ne_zero ht.ne' hp.ne'
      have harg : 0<1+(t*x)⁻¹ := by positivity
      have heq : 1+t*x=(t*x)*(1+(t*x)⁻¹) := by
        rw [mul_add,mul_one,mul_inv_cancel₀ htx]
        ring
      unfold positiveModeOffsetError positiveSpectrumLog
      rw [if_pos hp,one_mul,heq,Real.log_mul htx harg.ne',Real.log_mul ht.ne' hp.ne']
      simp only [if_pos hp]
      ring
    have hgap : Tendsto (fun t : ℝ => x⁻¹-t*positiveModeOffsetError x t) atTop (𝓝 0) := by
      have hK : Tendsto (fun t : ℝ => (1/(2*x^2))/t) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      apply squeeze_zero' ?_ ?_ hK
      · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
        have hh := (scaled_log_inverse_first_correction_bounds t x ht hp).1
        rwa [← he t ht] at hh
      · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
        have hh := (scaled_log_inverse_first_correction_bounds t x ht hp).2
        rw [← he t ht] at hh
        convert hh using 1 <;> field_simp [ht.ne',hp.ne'] <;> ring
    have hs := (tendsto_const_nhds : Tendsto (fun _t : ℝ => x⁻¹) atTop (𝓝 x⁻¹)).sub hgap
    simpa only [sub_sub_cancel,sub_zero] using hs
  · have hz : x=0 := le_antisymm (le_of_not_gt hp) hx
    subst x
    simpa [positiveModeOffsetError,positiveSpectrumLog] using
      (tendsto_const_nhds : Tendsto (fun _t : ℝ => (0 : ℝ)) atTop (𝓝 0))

end
end JinWishart
#print axioms JinWishart.positiveModeOffsetError_scaled_tendsto
