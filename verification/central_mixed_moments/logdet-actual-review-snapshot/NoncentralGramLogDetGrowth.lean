import JinWishartFormalization.GaussianGramLogMoments
import JinWishartFormalization.FiniteSpectrumLogDetGrowth

/-! Actual arbitrary fixed-mean Gaussian full-spectrum log statistic.
Codex. Natural logarithms. Not a derivation of channel mutual information.
[需人工审查] Expected log-det, full-rank and channel interpretation.
-/
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace JinWishart
noncomputable section

def actualNoncentralGramLogDet {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ)
    (r : ℝ) (z : ComplexSample (m := m) (n := n)) : ℝ :=
  finiteSpectrumLogDet (fun i => complexNoncentralSampleEigenvalue M i z) r

theorem integrable_actualNoncentralGramLogDet {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (r : ℝ) (hr : 0 ≤ r) :
    Integrable (actualNoncentralGramLogDet M r) (stdGaussian _) := by
  unfold actualNoncentralGramLogDet finiteSpectrumLogDet
  exact integrable_finsetSum Finset.univ (fun i _ =>
    integrable_log_one_add_mul _ _ (integrable_actualNoncentralEigenvalue M i)
      (ae_of_all _ (complexNoncentralSampleEigenvalue_nonneg M i)) r hr)

theorem actualNoncentralGramLogDet_expected_offset {m n : ℕ} (hn : 0 < n) (hnm : n ≤ m)
    (M : Matrix (Fin m) (Fin n) ℂ) :
    Tendsto (fun r : ℝ => (∫ z, actualNoncentralGramLogDet M r z ∂stdGaussian _)-
      (n : ℝ)*Real.log r) atTop
      (𝓝 (∑ i, ∫ z, Real.log (complexNoncentralSampleEigenvalue M i z) ∂stdGaussian _)) := by
  simpa only [Fintype.card_fin,actualNoncentralGramLogDet] using
    integral_finiteSpectrumLogDet_offset_tendsto (stdGaussian _) (complexNoncentralSampleEigenvalue M)
      (integrable_actualNoncentralEigenvalue M) (fun i =>
        (actualNoncentral_minimum_pos_ae hn hnm M).mono (fun z hz =>
          hz.trans_le (actualNoncentralMinimum_le_eigenvalue hn M i z)))
      (integrable_actualNoncentral_logEigenvalue hn hnm M)

theorem actualNoncentralGramLogDet_expected_prelog {m n : ℕ} (hn : 0 < n) (hnm : n ≤ m)
    (M : Matrix (Fin m) (Fin n) ℂ) :
    Tendsto (fun r : ℝ => (∫ z, actualNoncentralGramLogDet M r z ∂stdGaussian _)/Real.log r)
      atTop (𝓝 (n : ℝ)) := by
  simpa only [Fintype.card_fin,actualNoncentralGramLogDet] using
    integral_finiteSpectrumLogDet_prelog (stdGaussian _) (complexNoncentralSampleEigenvalue M)
      (integrable_actualNoncentralEigenvalue M) (fun i =>
        (actualNoncentral_minimum_pos_ae hn hnm M).mono (fun z hz =>
          hz.trans_le (actualNoncentralMinimum_le_eigenvalue hn M i z)))
      (integrable_actualNoncentral_logEigenvalue hn hnm M)

end
end JinWishart
#print axioms JinWishart.integrable_actualNoncentralGramLogDet
#print axioms JinWishart.actualNoncentralGramLogDet_expected_offset
#print axioms JinWishart.actualNoncentralGramLogDet_expected_prelog
