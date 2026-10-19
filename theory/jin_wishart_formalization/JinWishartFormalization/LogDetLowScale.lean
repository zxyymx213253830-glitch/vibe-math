import JinWishartFormalization.ActualLogDetMeanBound
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-! Low-scale full expected log-det slope is the actual mean trace.
Codex. No full-rank or inverse-moment assumption.
[需人工审查] Dominated convergence, actual variance and channel interpretation.
-/
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace JinWishart
noncomputable section

theorem integral_log_one_add_mul_low_scale {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (hf : Integrable f μ)
    (hnonneg : ∀ᵐ a ∂μ, 0 ≤ f a) :
    Tendsto (fun r : ℝ => (∫ a, Real.log (1+r*f a) ∂μ)/r) (𝓝[>] 0)
      (𝓝 (∫ a, f a ∂μ)) := by
  have ht : Tendsto (fun r : ℝ => ∫ a, Real.log (1+r*f a)/r ∂μ) (𝓝[>] 0)
      (𝓝 (∫ a, f a ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence f
    · exact Filter.Eventually.of_forall (fun r =>
        ((Real.measurable_log.comp_aemeasurable
          (aemeasurable_const.add (aemeasurable_const.mul hf.aemeasurable))).div_const r).aestronglyMeasurable)
    · filter_upwards [self_mem_nhdsWithin] with r hr
      change 0 < r at hr
      filter_upwards [hnonneg] with a ha
      have hpos : 0 < 1+r*f a := by positivity
      have hlog : 0 ≤ Real.log (1+r*f a) := Real.log_nonneg (by nlinarith)
      rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg hlog hr.le)]
      apply (div_le_iff₀ hr).mpr
      have h := Real.log_le_sub_one_of_pos hpos
      nlinarith
    · exact hf
    · exact ae_of_all _ (fun a => by
        have h := (Real.tendsto_mul_log_one_add_div_atTop (f a)).comp tendsto_inv_nhdsGT_zero
        apply h.congr'
        exact Filter.Eventually.of_forall (fun r => by
          simp only [Function.comp_apply,div_eq_mul_inv,inv_inv,mul_comm]))
  simpa only [integral_div] using ht

theorem integral_finiteSpectrumLogDet_low_scale {α ι : Type*}
    [MeasurableSpace α] [Fintype ι] (μ : Measure α)
    (f : ι → α → ℝ) (hf : ∀ i, Integrable (f i) μ)
    (hnonneg : ∀ i, ∀ᵐ a ∂μ, 0 ≤ f i a) :
    Tendsto (fun r : ℝ => (∫ a, finiteSpectrumLogDet (fun i => f i a) r ∂μ)/r) (𝓝[>] 0)
      (𝓝 (∑ i, ∫ a, f i a ∂μ)) := by
  classical
  have ht := tendsto_finsetSum Finset.univ (fun i _ =>
    integral_log_one_add_mul_low_scale μ (f i) (hf i) (hnonneg i))
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  change 0 < r at hr
  rw [show (∫ a, finiteSpectrumLogDet (fun i => f i a) r ∂μ)=
      ∑ i, ∫ a, Real.log (1+r*f i a) ∂μ from integral_finsetSum _ (fun i _ =>
        integrable_log_one_add_mul μ (f i) (hf i) (hnonneg i) r hr.le)]
  exact (Finset.sum_div _ _ _).symm

theorem actualNoncentralMatrixLogDet_low_scale {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) :
    Tendsto (fun r : ℝ => (∫ z, actualNoncentralMatrixLogDet M r z ∂stdGaussian _)/r) (𝓝[>] 0)
      (𝓝 (actualExpectedGramPower M)) := by
  rw [← sum_integral_actualNoncentralEigenvalues_eq_power M]
  have ht := integral_finiteSpectrumLogDet_low_scale (stdGaussian _) (complexNoncentralSampleEigenvalue M)
    (integrable_actualNoncentralEigenvalue M)
    (fun i => ae_of_all _ (complexNoncentralSampleEigenvalue_nonneg M i))
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  change 0 < r at hr
  have he : (fun z => finiteSpectrumLogDet (fun i => complexNoncentralSampleEigenvalue M i z) r) =
      actualNoncentralMatrixLogDet M r := funext (actualNoncentralGramLogDet_eq_matrix M r hr.le)
  rw [he]

end
end JinWishart
#print axioms JinWishart.integral_log_one_add_mul_low_scale
#print axioms JinWishart.integral_finiteSpectrumLogDet_low_scale
#print axioms JinWishart.actualNoncentralMatrixLogDet_low_scale
