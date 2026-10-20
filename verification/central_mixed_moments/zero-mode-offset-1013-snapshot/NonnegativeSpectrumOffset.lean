import JinWishartFormalization.NonnegativeSpectrumPrelog

/-! Zero modes in expected logdet offsets: positive log moments are explicit premises.
Codex. This does NOT prove those moments for arbitrary singular Gaussian factors.
[需人工审查] Restriction to positive modes, integral algebra and dominated convergence.
-/
open MeasureTheory Filter Set
open scoped Topology
namespace JinWishart
noncomputable section

def positiveSpectrumLog (x : ℝ) : ℝ := if 0<x then Real.log x else 0

theorem integral_log_one_add_mul_offset_nonneg {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (f : α → ℝ) (hm : Measurable f)
    (hf : Integrable f μ) (hn : ∀ᵐ a ∂μ, 0≤f a)
    (hlog : Integrable (fun a => positiveSpectrumLog (f a)) μ) :
    Tendsto (fun r : ℝ => (∫ a, Real.log (1+r*f a) ∂μ)-
      μ.real {a | 0<f a}*Real.log r) atTop
      (𝓝 (∫ a, positiveSpectrumLog (f a) ∂μ)) := by
  let S := {a | 0<f a}
  have hS : MeasurableSet S := measurableSet_lt measurable_const hm
  have hp : ∀ᵐ a ∂μ.restrict S, 0<f a := ae_restrict_mem hS
  have hl : Integrable (fun a => Real.log (f a)) (μ.restrict S) := by
    apply hlog.restrict.congr
    filter_upwards [hp] with a ha
    simp [positiveSpectrumLog,ha]
  have he : (∫ a, positiveSpectrumLog (f a) ∂μ)=∫ a, Real.log (f a) ∂μ.restrict S := by
    rw [← integral_indicator hS]
    apply integral_congr_ae
    exact ae_of_all _ (fun a => by simp [S,positiveSpectrumLog,Set.indicator_apply])
  rw [he]
  have ht := integral_log_add_inverse_tendsto (μ.restrict S) f hf.restrict hp hl
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1:ℝ)] with r hr
  have hrp : 0<r := zero_lt_one.trans_le hr
  have hC : (∫ a, Real.log (1+r*f a) ∂μ)=∫ a, Real.log (1+r*f a) ∂μ.restrict S := by
    rw [← integral_indicator hS]
    apply integral_congr_ae
    filter_upwards [hn] with a ha
    by_cases hpa : 0<f a
    · simp [S,hpa]
    · have hz : f a=0 := le_antisymm (le_of_not_gt hpa) ha
      simp [S,hz]
  have hi := integrable_log_one_add_mul (μ.restrict S) f hf.restrict
    (hp.mono (fun _ h => h.le)) r hrp.le
  have hconst : (μ.restrict S).real univ=μ.real S := by
    simp [Measure.real]
  rw [hC]
  symm
  calc
    _ = ∫ a, (Real.log (1+r*f a)-Real.log r) ∂μ.restrict S := by
      rw [integral_sub (f := fun a => Real.log (1+r*f a)) (g := fun _ => Real.log r)
        hi (integrable_const _),integral_const,hconst,smul_eq_mul]
    _ = _ := integral_congr_ae (hp.mono (fun a ha => by
      have harg : 0<f a+r⁻¹ := by positivity
      change Real.log (1+r*f a)-Real.log r=Real.log (f a+r⁻¹)
      rw [show 1+r*f a=r*(f a+r⁻¹) by field_simp [hrp.ne']; ring,
        Real.log_mul hrp.ne' harg.ne']
      ring))

theorem integral_finiteSpectrumLogDet_offset_nonneg {α ι : Type*}
    [MeasurableSpace α] [Fintype ι] (μ : Measure α) [IsFiniteMeasure μ]
    (f : ι → α → ℝ) (hm : ∀ i, Measurable (f i)) (hf : ∀ i, Integrable (f i) μ)
    (hn : ∀ i, ∀ᵐ a ∂μ, 0≤f i a)
    (hlog : ∀ i, Integrable (fun a => positiveSpectrumLog (f i a)) μ) :
    Tendsto (fun r : ℝ => (∫ a, finiteSpectrumLogDet (fun i => f i a) r ∂μ)-
      (∑ i, μ.real {a | 0<f i a})*Real.log r) atTop
      (𝓝 (∑ i, ∫ a, positiveSpectrumLog (f i a) ∂μ)) := by
  classical
  have ht := tendsto_finsetSum Finset.univ (fun i _ =>
    integral_log_one_add_mul_offset_nonneg μ (f i) (hm i) (hf i) (hn i) (hlog i))
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with r hr
  rw [show (∫ a, finiteSpectrumLogDet (fun i => f i a) r ∂μ)=
      ∑ i, ∫ a, Real.log (1+r*f i a) ∂μ from
      integral_finsetSum _ (fun i _ => integrable_log_one_add_mul μ (f i) (hf i) (hn i) r hr)]
  simp only [Finset.sum_sub_distrib,Finset.sum_mul]

end
end JinWishart
#print axioms JinWishart.integral_log_one_add_mul_offset_nonneg
#print axioms JinWishart.integral_finiteSpectrumLogDet_offset_nonneg
