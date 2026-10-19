import JinWishartFormalization.LogMomentIntegrability

/-! Finite spectral log sum: integrability, high-scale offset and prelog.
Codex. This is an abstract finite-spectrum theorem, not a channel coding theorem.
[需人工审查] Probability integral and limit interpretation.
-/
open MeasureTheory Filter
open scoped Topology
namespace JinWishart
noncomputable section

def finiteSpectrumLogDet {ι : Type*} [Fintype ι] (l : ι → ℝ) (r : ℝ) : ℝ :=
  ∑ i, Real.log (1+r*l i)

theorem integrable_finiteSpectrumLogDet {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (μ : Measure α) (f : ι → α → ℝ) (hf : ∀ i, Integrable (f i) μ)
    (hpos : ∀ i, ∀ᵐ a ∂μ, 0 < f i a) (r : ℝ) (hr : 0 ≤ r) :
    Integrable (fun a => finiteSpectrumLogDet (fun i => f i a) r) μ := by
  exact integrable_finsetSum _ (fun i _ =>
    integrable_log_one_add_mul μ (f i) (hf i) ((hpos i).mono (fun _ h => h.le)) r hr)

theorem integral_finiteSpectrumLogDet_offset_tendsto {α ι : Type*}
    [MeasurableSpace α] [Fintype ι] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : ι → α → ℝ) (hf : ∀ i, Integrable (f i) μ)
    (hpos : ∀ i, ∀ᵐ a ∂μ, 0 < f i a)
    (hlog : ∀ i, Integrable (fun a => Real.log (f i a)) μ) :
    Tendsto (fun r : ℝ => (∫ a, finiteSpectrumLogDet (fun i => f i a) r ∂μ)-
      (Fintype.card ι : ℝ)*Real.log r) atTop
      (𝓝 (∑ i, ∫ a, Real.log (f i a) ∂μ)) := by
  classical
  have ht := tendsto_finsetSum Finset.univ (fun i _ =>
    integral_log_add_inverse_tendsto μ (f i) (hf i) (hpos i) (hlog i))
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  have hrp : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hi (i : ι) := integrable_log_one_add_mul μ (f i) (hf i)
    ((hpos i).mono (fun _ h => h.le)) r hrp.le
  have he (i : ι) : (∫ a, Real.log (1+r*f i a) ∂μ)-Real.log r =
      ∫ a, Real.log (f i a+r⁻¹) ∂μ := by
    calc
      _ = ∫ a, (Real.log (1+r*f i a)-Real.log r) ∂μ := by
        rw [integral_sub (hi i) (integrable_const _)]
        simp
      _ = _ := integral_congr_ae ((hpos i).mono (fun a ha => by
        have hp : 0 < f i a+r⁻¹ := by positivity
        change Real.log (1+r*f i a)-Real.log r = Real.log (f i a+r⁻¹)
        rw [show 1+r*f i a=r*(f i a+r⁻¹) by field_simp [hrp.ne']; ring,
          Real.log_mul hrp.ne' hp.ne']
        ring))
  rw [show (∫ a, finiteSpectrumLogDet (fun i => f i a) r ∂μ)=
      ∑ i, ∫ a, Real.log (1+r*f i a) ∂μ from integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [← he]
  simp [Finset.sum_sub_distrib]

theorem integral_finiteSpectrumLogDet_prelog {α ι : Type*}
    [MeasurableSpace α] [Fintype ι] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : ι → α → ℝ) (hf : ∀ i, Integrable (f i) μ)
    (hpos : ∀ i, ∀ᵐ a ∂μ, 0 < f i a)
    (hlog : ∀ i, Integrable (fun a => Real.log (f i a)) μ) :
    Tendsto (fun r : ℝ => (∫ a, finiteSpectrumLogDet (fun i => f i a) r ∂μ)/Real.log r)
      atTop (𝓝 (Fintype.card ι : ℝ)) := by
  have ht := (integral_finiteSpectrumLogDet_offset_tendsto μ f hf hpos hlog).div_atTop
    Real.tendsto_log_atTop
  have hs := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (Fintype.card ι : ℝ))
    atTop (𝓝 (Fintype.card ι : ℝ))).add ht
  apply (show Tendsto (fun r : ℝ => (Fintype.card ι : ℝ)+
      ((∫ a, finiteSpectrumLogDet (fun i => f i a) r ∂μ)-
        (Fintype.card ι : ℝ)*Real.log r)/Real.log r) atTop
      (𝓝 (Fintype.card ι : ℝ)) by simpa using hs).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr
  have hlogr := (Real.log_pos hr).ne'
  field_simp
  <;> ring

end
end JinWishart
#print axioms JinWishart.integrable_finiteSpectrumLogDet
#print axioms JinWishart.integral_finiteSpectrumLogDet_offset_tendsto
#print axioms JinWishart.integral_finiteSpectrumLogDet_prelog
