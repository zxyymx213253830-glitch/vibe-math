import JinWishartFormalization.PositiveSpectrumFatouDivergence
import JinWishartFormalization.ActualPositiveSecondCoefficient

/-! Fatou transport for the scaled second positive-spectrum gap.
Codex. Seed2026102245 controls precede source; finite controls are not proof.
[需人工审查] AE pointwise limits, countably generated real filter and Fatou. -/
open MeasureTheory Filter
open scoped Topology
namespace JinWishart
noncomputable section

theorem positiveSpectrum_second_gap_lintegral_tendsto_top {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (μ : Measure Ω) (x : ι → Ω → ℝ)
    (hm : ∀ i,Measurable (x i)) (hx : ∀ i,∀ᵐ z ∂μ,0≤x i z)
    (hInv : (∫⁻ z,ENNReal.ofReal ((∑ i,((x i z)⁻¹)^2)/2) ∂μ)=⊤) :
    Tendsto (fun t : ℝ => ∫⁻ z,ENNReal.ofReal
      (∑ i,t*((x i z)⁻¹-t*positiveModeOffsetError (x i z) t)) ∂μ) atTop (𝓝 ⊤) := by
  classical
  have hmeas (t : ℝ) : Measurable (fun z => ENNReal.ofReal
      (∑ i,t*((x i z)⁻¹-t*positiveModeOffsetError (x i z) t))) := by
    apply ENNReal.continuous_ofReal.measurable.comp
    apply Finset.measurable_sum
    intro i _
    have hb : Measurable (fun z => if 0<x i z then (1 : ℝ) else 0) :=
      Measurable.ite (measurableSet_lt measurable_const (hm i)) measurable_const measurable_const
    have hl : Measurable (fun z => positiveSpectrumLog (x i z)) := by
      unfold positiveSpectrumLog
      exact Measurable.ite (measurableSet_lt measurable_const (hm i)) (hm i).log measurable_const
    have he : Measurable (fun z => positiveModeOffsetError (x i z) t) :=
      ((measurable_const.add (measurable_const.mul (hm i))).log.sub
        (hb.mul_const (Real.log t))).sub hl
    exact ((hm i).inv.sub (he.const_mul t)).const_mul t
  have hlim : ∀ᵐ z ∂μ,liminf (fun t : ℝ => ENNReal.ofReal
      (∑ i,t*((x i z)⁻¹-t*positiveModeOffsetError (x i z) t))) atTop=
      ENNReal.ofReal ((∑ i,((x i z)⁻¹)^2)/2) := by
    filter_upwards [ae_all_iff.mpr hx] with z hz
    have hs := tendsto_finsetSum Finset.univ (fun i _ =>
      positiveModeOffsetError_second_scaled_tendsto (x i z) (hz i))
    have hs' : Tendsto (fun t : ℝ => ∑ i,t*((x i z)⁻¹-t*positiveModeOffsetError (x i z) t))
        atTop (𝓝 ((∑ i,((x i z)⁻¹)^2)/2)) := by
      simpa only [Finset.sum_div] using hs
    exact ((ENNReal.continuous_ofReal.tendsto _).comp hs').liminf_eq
  have hFatou := lintegral_liminf_le (μ := μ) (u := (atTop : Filter ℝ)) hmeas
  rw [lintegral_congr_ae hlim,hInv] at hFatou
  exact tendsto_of_le_liminf_of_limsup_le hFatou le_top

end
end JinWishart
#print axioms JinWishart.positiveSpectrum_second_gap_lintegral_tendsto_top
