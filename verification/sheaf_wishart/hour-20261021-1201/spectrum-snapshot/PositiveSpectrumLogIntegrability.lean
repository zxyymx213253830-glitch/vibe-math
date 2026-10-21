import JinWishartFormalization.CorrelatedConditionalOffset

/-! Aggregate positive-spectrum log L1 implies each mode's L1, provided the
nonnegative spectrum has integrable trace. This does NOT supply aggregate L1
for arbitrary singular Wishart parameters. Codex.
[需人工审查] AE nonnegativity, integrability domination and model interpretation.
-/
open Matrix MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace JinWishart
noncomputable section

theorem positiveSpectrumLog_le_self {x : ℝ} (hx : 0≤x) : positiveSpectrumLog x ≤ x := by
  by_cases hp : 0<x
  · rw [positiveSpectrumLog,if_pos hp]
    linarith [Real.log_le_sub_one_of_pos hp]
  · simp only [positiveSpectrumLog,if_neg hp]
    exact hx

theorem abs_positiveSpectrumLog_le_trace_add_abs_sum {ι : Type*} [Fintype ι]
    (f : ι → ℝ) (hn : ∀ i, 0≤f i) (i : ι) :
    |positiveSpectrumLog (f i)| ≤ (∑ j, f j)+|∑ j, positiveSpectrumLog (f j)| := by
  classical
  have hu (j : ι) := positiveSpectrumLog_le_self (hn j)
  have hs : f i ≤ ∑ j, f j := Finset.single_le_sum (fun j _ => hn j) (Finset.mem_univ i)
  have hg : f i-positiveSpectrumLog (f i) ≤
      (∑ j, f j)-(∑ j, positiveSpectrumLog (f j)) := by
    simpa only [Finset.sum_sub_distrib] using
      (Finset.single_le_sum (fun j _ => sub_nonneg.mpr (hu j)) (Finset.mem_univ i))
  apply abs_le.mpr
  constructor
  · linarith [hn i,neg_le_abs (∑ j, positiveSpectrumLog (f j))]
  · linarith [hu i,abs_nonneg (∑ j, positiveSpectrumLog (f j))]

theorem integrable_positiveSpectrumLog_of_sum {α ι : Type*}
    [MeasurableSpace α] [Fintype ι] (μ : Measure α)
    (f : ι → α → ℝ) (hm : ∀ i, Measurable (f i))
    (hf : ∀ i, Integrable (f i) μ) (hn : ∀ i, ∀ᵐ a ∂μ, 0≤f i a)
    (hSum : Integrable (fun a => ∑ i, positiveSpectrumLog (f i a)) μ) (i : ι) :
    Integrable (fun a => positiveSpectrumLog (f i a)) μ := by
  classical
  have ht : Integrable (fun a => ∑ i, f i a) μ :=
    integrable_finsetSum _ (fun i _ => hf i)
  have hmeas : Measurable (fun a => positiveSpectrumLog (f i a)) :=
    Measurable.ite (measurableSet_lt measurable_const (hm i)) (hm i).log measurable_const
  apply (ht.add hSum.norm).mono' hmeas.aestronglyMeasurable
  have ha : ∀ᵐ a ∂μ, ∀ j, 0≤f j a := ae_all_iff.mpr hn
  filter_upwards [ha] with a hna
  simpa only [Real.norm_eq_abs,Pi.add_apply] using
    abs_positiveSpectrumLog_le_trace_add_abs_sum (fun j => f j a) hna i

theorem actualCorrelatedMatrixLogDet_offset_of_sum_log {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (hSum : Integrable (fun z => ∑ i, positiveSpectrumLog (actualCorrelatedEigenvalue B M i z))
      (stdGaussian (ComplexSample (m := m) (n := p)))) :
    Tendsto (fun r : ℝ => (∫ z, actualCorrelatedMatrixLogDet B M r z ∂stdGaussian _)-
      ((min m (Matrix.fromRows B M).rank):ℝ)*Real.log r) atTop
      (𝓝 (∫ z, (∑ i, positiveSpectrumLog (actualCorrelatedEigenvalue B M i z)) ∂stdGaussian _)) := by
  apply actualCorrelatedMatrixLogDet_offset_of_log_moments B M
  exact integrable_positiveSpectrumLog_of_sum (stdGaussian _)
    (actualCorrelatedEigenvalue B M) (measurable_actualCorrelatedEigenvalue B M)
    (integrable_actualCorrelatedEigenvalue B M)
    (fun i => ae_of_all _ (actualCorrelatedEigenvalue_nonneg B M i)) hSum

end
end JinWishart
#print axioms JinWishart.positiveSpectrumLog_le_self
#print axioms JinWishart.abs_positiveSpectrumLog_le_trace_add_abs_sum
#print axioms JinWishart.integrable_positiveSpectrumLog_of_sum
#print axioms JinWishart.actualCorrelatedMatrixLogDet_offset_of_sum_log
