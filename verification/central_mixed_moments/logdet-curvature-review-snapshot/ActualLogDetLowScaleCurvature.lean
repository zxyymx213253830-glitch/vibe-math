import JinWishartFormalization.ActualGaussianTraceMean
import JinWishartFormalization.LogDetLowScaleSecondOrder

/-! Second-order low-scale full logdet for every actual fixed-mean Gaussian shape.
Codex. The second spectral moment is its finite actual integral, not an assumed
closed formula. No rank or inverse moment condition. Natural logarithms.
[需人工审查] Gaussian L4, spectral domination and interchange of limit/integral.
-/
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace JinWishart
noncomputable section

theorem integrable_actualNoncentralGram_trace_sq {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) :
    Integrable (fun z : ComplexSample (m := m) (n := n) =>
      ((complexGram (complexSampleMatrix z+M)).trace.re)^2) (stdGaussian _) := by
  have hid : MemLp (id : ComplexSample (m := m) (n := n) → ComplexSample)
      4 (stdGaussian _) := IsGaussian.memLp_id _ _ (by norm_num)
  have hc : MemLp (fun _ : ComplexSample (m := m) (n := n) => complexSampleMean M)
      4 (stdGaussian _) := memLp_const _
  have hi := (hid.add hc).integrable_norm_pow' (p := 4)
  have he (z : ComplexSample (m := m) (n := n)) :
      ((complexGram (complexSampleMatrix z+M)).trace.re)^2 = ‖z+complexSampleMean M‖^4/4 := by
    have h := complexSampleGram_trace_half_norm (z+complexSampleMean M)
    simp only [complexSampleGram,complexSampleMatrix_add_mean] at h
    rw [h]
    ring
  simp_rw [he]
  exact hi.div_const 4

theorem integrable_actualNoncentralEigenvalue_sq {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (i : Fin (Fintype.card (Fin n))) :
    Integrable (fun z => (complexNoncentralSampleEigenvalue M i z)^2) (stdGaussian _) := by
  apply (integrable_actualNoncentralGram_trace_sq M).mono' (by
    exact ((measurable_actualNoncentralEigenvalue M i).pow_const 2).aestronglyMeasurable)
  exact ae_of_all _ (fun z => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (complexNoncentralSampleEigenvalue_nonneg M i z)
      (actualNoncentralEigenvalue_le_trace M i z) 2)

theorem actualNoncentralMatrixLogDet_low_scale_curvature {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) :
    Tendsto (fun r : ℝ =>
      (r*((m*n : ℕ)+∑ i, ∑ j, ‖M i j‖^2)-
        (∫ z, actualNoncentralMatrixLogDet M r z ∂stdGaussian _))/r^2)
      (𝓝[>] 0)
      (𝓝 ((∑ i, ∫ z, (complexNoncentralSampleEigenvalue M i z)^2 ∂stdGaussian _)/2)) := by
  have ht := integral_finiteSpectrumLogDet_second_order (stdGaussian _)
    (complexNoncentralSampleEigenvalue M) (integrable_actualNoncentralEigenvalue M)
    (integrable_actualNoncentralEigenvalue_sq M)
    (fun i => ae_of_all _ (complexNoncentralSampleEigenvalue_nonneg M i))
  rw [sum_integral_actualNoncentralEigenvalues_eq_power M,actualExpectedGramPower_eq_closed] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hrp : 0 < r := hr
  have he : (fun z => finiteSpectrumLogDet (fun i => complexNoncentralSampleEigenvalue M i z) r) =
      actualNoncentralMatrixLogDet M r := funext (actualNoncentralGramLogDet_eq_matrix M r hrp.le)
  rw [he]

end
end JinWishart
#print axioms JinWishart.integrable_actualNoncentralGram_trace_sq
#print axioms JinWishart.integrable_actualNoncentralEigenvalue_sq
#print axioms JinWishart.actualNoncentralMatrixLogDet_low_scale_curvature
