import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Elementary second-moment continuity from mean-square convergence.
This packages existing Holder/Cauchy-Schwarz, not new integration theory.
Codex. [需人工审查] Integrability and limit interpretation. -/
open MeasureTheory Filter
open scoped Topology
namespace JinWishart
noncomputable section

theorem integral_square_difference_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (u v : α→ℝ) (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    |(∫ a,(u a)^2 ∂μ)-(∫ a,(v a)^2 ∂μ)|≤
      (∫ a,(u a-v a)^2 ∂μ)+2*Real.sqrt (∫ a,(u a-v a)^2 ∂μ)*Real.sqrt (∫ a,(v a)^2 ∂μ) := by
  let e := fun a=>u a-v a
  have he : MemLp e 2 μ := hu.sub hv
  have hcross : Integrable (fun a=>e a*v a) μ := he.integrable_mul hv
  have hholder : (∫ a,‖e a‖*‖v a‖ ∂μ)≤Real.sqrt (∫ a,(e a)^2 ∂μ)*Real.sqrt (∫ a,(v a)^2 ∂μ) := by
    have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
      (by simpa using he : MemLp e (ENNReal.ofReal (2:ℝ)) μ)
      (by simpa using hv : MemLp v (ENNReal.ofReal (2:ℝ)) μ)
    simpa [Real.rpow_two,Real.sqrt_eq_rpow,Real.norm_eq_abs] using h
  have hb : |∫ a,e a*v a ∂μ|≤Real.sqrt (∫ a,(e a)^2 ∂μ)*Real.sqrt (∫ a,(v a)^2 ∂μ) := by
    calc
      _ ≤ ∫ a,‖e a*v a‖ ∂μ := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun a=>e a*v a)
      _ = ∫ a,‖e a‖*‖v a‖ ∂μ := integral_congr_ae (ae_of_all _ (fun a=>norm_mul _ _))
      _ ≤ _ := hholder
  have hid : (∫ a,(u a)^2 ∂μ)-(∫ a,(v a)^2 ∂μ)=
      (∫ a,(e a)^2 ∂μ)+2*(∫ a,e a*v a ∂μ) := by
    rw [← integral_sub hu.integrable_sq hv.integrable_sq]
    calc
      _ = ∫ a,(e a)^2+2*(e a*v a) ∂μ := by
        apply integral_congr_ae
        exact ae_of_all _ (fun a=>by dsimp only [e]; ring)
      _ = _ := by rw [integral_add he.integrable_sq (hcross.const_mul 2),integral_const_mul]
  rw [hid]
  have hn : 0≤∫ a,(e a)^2 ∂μ := integral_nonneg (fun a=>sq_nonneg _)
  calc
    _ ≤ |∫ a,(e a)^2 ∂μ|+|2*(∫ a,e a*v a ∂μ)| := abs_add_le _ _
    _ = (∫ a,(e a)^2 ∂μ)+2*|∫ a,e a*v a ∂μ| := by rw [abs_of_nonneg hn,abs_mul]; norm_num
    _ ≤ _ := by nlinarith only [hb]

theorem integral_square_tendsto_of_mean_square {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (u : ℝ→α→ℝ) (v : α→ℝ)
    (hu : ∀ r : ℝ,1≤r → MemLp (u r) 2 μ) (hv : MemLp v 2 μ)
    (hlim : Tendsto (fun r : ℝ=>∫ a,(u r a-v a)^2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun r : ℝ=>∫ a,(u r a)^2 ∂μ) atTop (𝓝 (∫ a,(v a)^2 ∂μ)) := by
  have hb : Tendsto (fun r : ℝ=>(∫ a,(u r a-v a)^2 ∂μ)+
      2*Real.sqrt (∫ a,(u r a-v a)^2 ∂μ)*Real.sqrt (∫ a,(v a)^2 ∂μ)) atTop (𝓝 0) := by
    simpa using hlim.add ((hlim.sqrt.const_mul 2).mul_const (Real.sqrt (∫ a,(v a)^2 ∂μ)))
  have hs : Tendsto (fun r : ℝ=>|(∫ a,(u r a)^2 ∂μ)-(∫ a,(v a)^2 ∂μ)|) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun r=>abs_nonneg _)) ?_ hb
    filter_upwards [eventually_ge_atTop (1:ℝ)] with r hr
    exact integral_square_difference_bound μ (u r) v (hu r hr) hv
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using hs)

end
end JinWishart
#print axioms JinWishart.integral_square_difference_bound
#print axioms JinWishart.integral_square_tendsto_of_mean_square
