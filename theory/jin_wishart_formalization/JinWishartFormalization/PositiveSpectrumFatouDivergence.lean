import JinWishartFormalization.PositiveModeFirstCoefficient
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! Nonnegative Fatou transport of an infinite reciprocal spectral integral
to the scaled offset. Codex. Controls seed2026102244 precede source.
[需人工审查] Countably generated scale filter, AE scalar limits and Fatou.
No finite-cutoff numerical estimate is treated as a divergence proof. -/
open MeasureTheory Filter
open scoped Topology
namespace JinWishart
noncomputable section

theorem positiveSpectrum_scaled_offset_lintegral_tendsto_top {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (μ : Measure Ω) (x : ι → Ω → ℝ)
    (hm : ∀ i,Measurable (x i)) (hx : ∀ i,∀ᵐ z ∂μ,0≤x i z)
    (hInv : (∫⁻ z,ENNReal.ofReal (∑ i,(x i z)⁻¹) ∂μ)=⊤) :
    Tendsto (fun t : ℝ => ∫⁻ z,ENNReal.ofReal (t*(∑ i,positiveModeOffsetError (x i z) t)) ∂μ)
      atTop (𝓝 ⊤) := by
  classical
  have hmeas (t : ℝ) : Measurable (fun z =>
      ENNReal.ofReal (t*(∑ i,positiveModeOffsetError (x i z) t))) := by
    have hs : Measurable (fun z => ∑ i,positiveModeOffsetError (x i z) t) := by
      apply Finset.measurable_sum
      intro i _
      have hb : Measurable (fun z => if 0<x i z then (1 : ℝ) else 0) :=
        Measurable.ite (measurableSet_lt measurable_const (hm i)) measurable_const measurable_const
      have hl : Measurable (fun z => positiveSpectrumLog (x i z)) := by
        unfold positiveSpectrumLog
        exact Measurable.ite (measurableSet_lt measurable_const (hm i)) (hm i).log measurable_const
      exact ((measurable_const.add (measurable_const.mul (hm i))).log.sub
        (hb.mul_const (Real.log t))).sub hl
    exact ENNReal.continuous_ofReal.measurable.comp (hs.const_mul t)
  have hlim : ∀ᵐ z ∂μ,liminf (fun t : ℝ =>
      ENNReal.ofReal (t*(∑ i,positiveModeOffsetError (x i z) t))) atTop=
      ENNReal.ofReal (∑ i,(x i z)⁻¹) := by
    filter_upwards [ae_all_iff.mpr hx] with z hz
    have hs := tendsto_finsetSum Finset.univ (fun i _ =>
      positiveModeOffsetError_scaled_tendsto (x i z) (hz i))
    have hs' : Tendsto (fun t : ℝ => t*(∑ i,positiveModeOffsetError (x i z) t))
        atTop (𝓝 (∑ i,(x i z)⁻¹)) := by simpa only [Finset.mul_sum] using hs
    exact ((ENNReal.continuous_ofReal.tendsto _).comp hs').liminf_eq
  have hFatou := lintegral_liminf_le (μ := μ) (u := (atTop : Filter ℝ)) hmeas
  rw [lintegral_congr_ae hlim,hInv] at hFatou
  exact tendsto_of_le_liminf_of_limsup_le hFatou le_top

end
end JinWishart
#print axioms JinWishart.positiveSpectrum_scaled_offset_lintegral_tendsto_top
