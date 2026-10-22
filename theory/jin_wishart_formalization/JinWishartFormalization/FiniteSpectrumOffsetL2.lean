import JinWishartFormalization.PositiveSpectrumLogIntegrability
import Mathlib.Algebra.Order.Chebyshev

/-! Mean-square high-scale offset for finite nonnegative spectra.
The measure is arbitrary; square-L1 hypotheses supply an integrable majorant.
Codex. [需人工审查] AE quantifiers and dominated convergence. -/
open MeasureTheory Filter Set
open scoped Topology
namespace JinWishart
noncomputable section

def positiveModeOffsetError (x r : ℝ) : ℝ :=
  Real.log (1+r*x)-(if 0<x then (1:ℝ) else 0)*Real.log r-positiveSpectrumLog x

theorem positiveModeOffsetError_nonneg_le (x r : ℝ) (hx : 0≤x) (hr : 1≤r) :
    0≤positiveModeOffsetError x r ∧ positiveModeOffsetError x r≤x+|positiveSpectrumLog x| := by
  have hrp : 0<r := zero_lt_one.trans_le hr
  by_cases hp : 0<x
  · have ha : 0<x+r⁻¹ := by positivity
    have he : Real.log (1+r*x)=Real.log r+Real.log (x+r⁻¹) := by
      rw [show 1+r*x=r*(x+r⁻¹) by field_simp [hrp.ne']; ring,
        Real.log_mul hrp.ne' ha.ne']
    have hl := Real.log_le_log hp (by have hi : 0≤r⁻¹ := inv_nonneg.mpr hrp.le; linarith : x≤x+r⁻¹)
    have hir : r⁻¹≤1 := (inv_le_one₀ hrp).2 hr
    have hu := Real.log_le_log ha (by linarith : x+r⁻¹≤x+1)
    have hb := Real.log_le_sub_one_of_pos (by positivity : 0<x+1)
    simp only [positiveModeOffsetError,positiveSpectrumLog,if_pos hp,one_mul]
    rw [he]
    constructor <;> linarith [neg_le_abs (Real.log x)]
  · have hz : x=0 := le_antisymm (le_of_not_gt hp) hx
    simp [positiveModeOffsetError,positiveSpectrumLog,hz]

theorem positiveModeOffsetError_tendsto (x : ℝ) (hx : 0≤x) :
    Tendsto (positiveModeOffsetError x) atTop (𝓝 0) := by
  by_cases hp : 0<x
  · have ha : Tendsto (fun r : ℝ=>x+r⁻¹) atTop (𝓝 x) := by
      simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℝ=>x) atTop (𝓝 x)).add tendsto_inv_atTop_zero)
    have hl := (Real.continuousAt_log hp.ne').tendsto.comp ha
    have ht : Tendsto (fun r : ℝ=>Real.log (x+r⁻¹)-Real.log x) atTop (𝓝 0) := by
      simpa using hl.sub_const (Real.log x)
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    have harg : 0<x+r⁻¹ := by positivity
    unfold positiveModeOffsetError
    rw [positiveSpectrumLog,if_pos hp,if_pos hp,one_mul,
      show 1+r*x=r*(x+r⁻¹) by field_simp [hr.ne']; ring,
      Real.log_mul hr.ne' harg.ne']
    ring
  · have hz : x=0 := le_antisymm (le_of_not_gt hp) hx
    have he : positiveModeOffsetError 0=(fun _r : ℝ=>(0:ℝ)) := by
      funext r
      simp [positiveModeOffsetError,positiveSpectrumLog]
    rw [hz,he]
    exact tendsto_const_nhds

theorem integral_finiteSpectrumOffsetError_sq_tendsto {α ι : Type*}
    [MeasurableSpace α] [Fintype ι] (μ : Measure α) (f : ι→α→ℝ)
    (hm : ∀ i,Measurable (f i)) (hn : ∀ i,∀ᵐ a ∂μ,0≤f i a)
    (hf : ∀ i,Integrable (fun a=>(f i a)^2) μ)
    (hlog : ∀ i,Integrable (fun a=>(positiveSpectrumLog (f i a))^2) μ) :
    (∀ r : ℝ,1≤r → Integrable (fun a=>(∑ i,positiveModeOffsetError (f i a) r)^2) μ) ∧
    Tendsto (fun r : ℝ=>∫ a,(∑ i,positiveModeOffsetError (f i a) r)^2 ∂μ) atTop (𝓝 0) := by
  classical
  let bound := fun a=>(Fintype.card ι : ℝ)*(∑ i,(2*(f i a)^2+2*(positiveSpectrumLog (f i a))^2))
  have hbound : Integrable bound μ :=
    (integrable_finsetSum Finset.univ (fun i _=>(hf i).const_mul 2 |>.add ((hlog i).const_mul 2))).const_mul _
  have hmeas (r : ℝ) : Measurable (fun a=>(∑ i,positiveModeOffsetError (f i a) r)^2) := by
    apply Measurable.pow_const
    apply Finset.measurable_sum
    intro i hi
    have hiM : Measurable (fun a=>if 0<f i a then (1:ℝ) else 0) := Measurable.ite (measurableSet_lt measurable_const (hm i))
      (measurable_const : Measurable (fun _a : α=>(1:ℝ))) (measurable_const : Measurable (fun _a : α=>(0:ℝ)))
    have hlM : Measurable (fun a=>positiveSpectrumLog (f i a)) := by
      unfold positiveSpectrumLog
      exact Measurable.ite (measurableSet_lt measurable_const (hm i)) (hm i).log measurable_const
    exact ((measurable_const.add (measurable_const.mul (hm i))).log.sub (hiM.mul_const (Real.log r))).sub hlM
  have ha : ∀ᵐ a ∂μ,∀ i,0≤f i a := ae_all_iff.mpr hn
  have hb (r : ℝ) (hr : 1≤r) : ∀ᵐ a ∂μ,‖(∑ i,positiveModeOffsetError (f i a) r)^2‖≤bound a := by
    filter_upwards [ha] with a hna
    have hs (i : ι) : (positiveModeOffsetError (f i a) r)^2≤2*(f i a)^2+2*(positiveSpectrumLog (f i a))^2 := by
      have he := positiveModeOffsetError_nonneg_le (f i a) r (hna i) hr
      have hp := pow_le_pow_left₀ he.1 he.2 2
      nlinarith only [hp,sq_abs (positiveSpectrumLog (f i a)),sq_nonneg (f i a-|positiveSpectrumLog (f i a)|)]
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    apply (_root_.sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i=>positiveModeOffsetError (f i a) r)).trans
    change (Fintype.card ι : ℝ)*(∑ i,(positiveModeOffsetError (f i a) r)^2)≤bound a
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact Finset.sum_le_sum (fun i _=>hs i)
  refine ⟨fun r hr=>hbound.mono' (hmeas r).aestronglyMeasurable (hb r hr),?_⟩
  have ht : Tendsto (fun r : ℝ=>∫ a,(∑ i,positiveModeOffsetError (f i a) r)^2 ∂μ) atTop (𝓝 (∫ _a : α,(0:ℝ) ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence bound
    · exact Eventually.of_forall (fun r=>(hmeas r).aestronglyMeasurable)
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with r hr
      exact hb r hr
    · exact hbound
    · filter_upwards [ha] with a hna
      have hs := tendsto_finsetSum Finset.univ (fun i _=>positiveModeOffsetError_tendsto (f i a) (hna i))
      simpa using hs.pow 2
  simpa using ht

end
end JinWishart
#print axioms JinWishart.positiveModeOffsetError_nonneg_le
#print axioms JinWishart.positiveModeOffsetError_tendsto
#print axioms JinWishart.integral_finiteSpectrumOffsetError_sq_tendsto
