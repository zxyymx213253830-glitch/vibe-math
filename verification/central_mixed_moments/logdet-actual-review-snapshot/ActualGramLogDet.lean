import JinWishartFormalization.NoncentralGramLogDetGrowth
import JinWishartFormalization.HermitianSpectralLogDet

/-! Full actual matrix log-det expectation, high-SNR prelog and finite offset.
Codex. Arbitrary fixed deterministic mean, iid variance-one CN noise, m>=N>0.
Natural units. This statistic is not itself a channel coding theorem.
[需人工审查] Measure/variance and communication-model correspondence.
-/
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace JinWishart
noncomputable section

def actualNoncentralMatrixLogDet {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ)
    (r : ℝ) (z : ComplexSample (m := m) (n := n)) : ℝ :=
  Real.log ((1+(r : ℂ) • complexGram (complexSampleMatrix z+M)).det.re)

theorem actualNoncentralGramLogDet_eq_matrix {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (r : ℝ) (hr : 0 ≤ r)
    (z : ComplexSample (m := m) (n := n)) :
    actualNoncentralGramLogDet M r z = actualNoncentralMatrixLogDet M r z := by
  exact (gram_real_logdet_eq_spectral (complexSampleMatrix z+M) r hr).symm

theorem integrable_actualNoncentralMatrixLogDet {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (r : ℝ) (hr : 0 ≤ r) :
    Integrable (actualNoncentralMatrixLogDet M r) (stdGaussian _) := by
  simpa only [← funext (actualNoncentralGramLogDet_eq_matrix M r hr)] using
    integrable_actualNoncentralGramLogDet M r hr

theorem actualNoncentral_logGramDet_eq_sum_log_ae {m n : ℕ} (hn : 0 < n) (hnm : n ≤ m)
    (M : Matrix (Fin m) (Fin n) ℂ) :
    (fun z : ComplexSample (m := m) (n := n) =>
      Real.log (complexGram (complexSampleMatrix z+M)).det.re) =ᵐ[stdGaussian _]
      (fun z => ∑ i, Real.log (complexNoncentralSampleEigenvalue M i z)) := by
  filter_upwards [actualNoncentral_minimum_pos_ae hn hnm M] with z hz
  exact hermitian_real_logdet_eq_sum_log _ (complexGram_posSemidef _).1 (fun i =>
    hz.trans_le (actualNoncentralMinimum_le_eigenvalue hn M i z))

theorem integrable_actualNoncentral_logGramDet {m n : ℕ} (hn : 0 < n) (hnm : n ≤ m)
    (M : Matrix (Fin m) (Fin n) ℂ) :
    Integrable (fun z : ComplexSample (m := m) (n := n) =>
      Real.log (complexGram (complexSampleMatrix z+M)).det.re) (stdGaussian _) := by
  apply (integrable_finsetSum Finset.univ (fun i _ =>
    integrable_actualNoncentral_logEigenvalue hn hnm M i)).congr
  exact (actualNoncentral_logGramDet_eq_sum_log_ae hn hnm M).symm

theorem actualNoncentralMatrixLogDet_expected_offset {m n : ℕ} (hn : 0 < n) (hnm : n ≤ m)
    (M : Matrix (Fin m) (Fin n) ℂ) :
    Tendsto (fun r : ℝ => (∫ z, actualNoncentralMatrixLogDet M r z ∂stdGaussian _)-
      (n : ℝ)*Real.log r) atTop
      (𝓝 (∫ z, Real.log (complexGram (complexSampleMatrix z+M)).det.re ∂stdGaussian _)) := by
  have he : (∫ z, Real.log (complexGram (complexSampleMatrix z+M)).det.re ∂stdGaussian _) =
      ∑ i, ∫ z, Real.log (complexNoncentralSampleEigenvalue M i z) ∂stdGaussian _ := by
    rw [integral_congr_ae (actualNoncentral_logGramDet_eq_sum_log_ae hn hnm M)]
    exact integral_finsetSum _ (fun i _ => integrable_actualNoncentral_logEigenvalue hn hnm M i)
  rw [he]
  apply (actualNoncentralGramLogDet_expected_offset hn hnm M).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
  simp only [← funext (actualNoncentralGramLogDet_eq_matrix M r hr)]

theorem actualNoncentralMatrixLogDet_expected_prelog {m n : ℕ} (hn : 0 < n) (hnm : n ≤ m)
    (M : Matrix (Fin m) (Fin n) ℂ) :
    Tendsto (fun r : ℝ => (∫ z, actualNoncentralMatrixLogDet M r z ∂stdGaussian _)/Real.log r)
      atTop (𝓝 (n : ℝ)) := by
  apply (actualNoncentralGramLogDet_expected_prelog hn hnm M).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
  simp only [← funext (actualNoncentralGramLogDet_eq_matrix M r hr)]

end
end JinWishart
#print axioms JinWishart.actualNoncentralGramLogDet_eq_matrix
#print axioms JinWishart.integrable_actualNoncentralMatrixLogDet
#print axioms JinWishart.actualNoncentral_logGramDet_eq_sum_log_ae
#print axioms JinWishart.integrable_actualNoncentral_logGramDet
#print axioms JinWishart.actualNoncentralMatrixLogDet_expected_offset
#print axioms JinWishart.actualNoncentralMatrixLogDet_expected_prelog
