import JinWishartFormalization.WideGaussianLogDet
import JinWishartFormalization.LogMeanBound

/-! Finite-scale full logdet expectation bound by the actual expected trace.
Codex. No full-rank premise needed. [需人工审查] Expectation/variance interpretation.
The trace is its actual integral, not an assumed or unproved closed mean formula.
-/
open Matrix MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

def actualExpectedGramPower {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) : ℝ :=
  ∫ z : ComplexSample (m := m) (n := n), (complexGram (complexSampleMatrix z+M)).trace.re ∂stdGaussian _

theorem sum_actualNoncentralEigenvalues_eq_trace {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (z : ComplexSample (m := m) (n := n)) :
    (∑ i, complexNoncentralSampleEigenvalue M i z) =
      (complexGram (complexSampleMatrix z+M)).trace.re := by
  classical
  let h := (complexGram_posSemidef (complexSampleMatrix z+M)).1
  let e : Fin (Fintype.card (Fin n)) ≃ Fin n :=
    Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))
  have hs : (∑ j, h.eigenvalues₀ j) = ∑ j, h.eigenvalues j := by
    simpa only [Matrix.IsHermitian.eigenvalues,e,Equiv.symm_apply_apply] using
      (Equiv.sum_comp e (fun j => h.eigenvalues j))
  have ht := congrArg Complex.re h.trace_eq_sum_eigenvalues
  simp only [Complex.re_sum] at ht
  change (complexGram (complexSampleMatrix z+M)).trace.re = ∑ j, h.eigenvalues j at ht
  exact hs.trans ht.symm

theorem sum_integral_actualNoncentralEigenvalues_eq_power {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) :
    (∑ i, ∫ z, complexNoncentralSampleEigenvalue M i z ∂stdGaussian _) = actualExpectedGramPower M := by
  rw [← integral_finsetSum _ (fun i _ => integrable_actualNoncentralEigenvalue M i)]
  exact integral_congr_ae (ae_of_all _ (sum_actualNoncentralEigenvalues_eq_trace M))

theorem actualExpectedGramPower_nonneg {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) :
    0 ≤ actualExpectedGramPower M := by
  rw [← sum_integral_actualNoncentralEigenvalues_eq_power M]
  exact Finset.sum_nonneg (fun i _ => integral_nonneg (complexNoncentralSampleEigenvalue_nonneg M i))

theorem actualExpectedGramPower_transpose {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) :
    actualExpectedGramPower M = actualExpectedGramPower Mᵀ := by
  let e : ComplexSample (m := m) (n := n) ≃ᵐ ComplexSample (m := n) (n := m) :=
    (complexSampleTransposeReindex m n).toHomeomorph.toMeasurableEquiv
  have hmap : (stdGaussian (ComplexSample (m := m) (n := n))).map e =
      stdGaussian (ComplexSample (m := n) (n := m)) := stdGaussian_map _
  have he (z : ComplexSample (m := m) (n := n)) :
      (complexGram (complexSampleMatrix z+M)).trace.re =
        (complexGram (complexSampleMatrix (e z)+Mᵀ)).trace.re := by
    change _ = (complexGram (complexSampleMatrix (complexSampleTransposeReindex m n z)+Mᵀ)).trace.re
    rw [complexSampleMatrix_transpose_reindex,← Matrix.transpose_add,complexGram_trace_re,complexGram_trace_re]
    simp only [Matrix.transpose_apply]
    exact Finset.sum_comm
  unfold actualExpectedGramPower
  calc
    _ = ∫ z, (complexGram (complexSampleMatrix (e z)+Mᵀ)).trace.re ∂stdGaussian _ :=
      integral_congr_ae (ae_of_all _ he)
    _ = _ := by
      have h := integral_map_equiv (μ := stdGaussian (ComplexSample (m := m) (n := n)))
        e (fun z => (complexGram (complexSampleMatrix z+Mᵀ)).trace.re)
      rw [hmap] at h
      exact h.symm

theorem actualNoncentralMatrixLogDet_column_mean_bound {m n : ℕ} (hn : 0 < n)
    (M : Matrix (Fin m) (Fin n) ℂ) (r : ℝ) (hr : 0 ≤ r) :
    (∫ z, actualNoncentralMatrixLogDet M r z ∂stdGaussian _) ≤
      (n : ℝ)*Real.log (1+r*actualExpectedGramPower M/(n : ℝ)) := by
  have h := integral_finiteSpectrumLogDet_mean_upper_bound (stdGaussian _)
    (by simpa using hn : 0 < Fintype.card (Fin (Fintype.card (Fin n))))
    (complexNoncentralSampleEigenvalue M) (integrable_actualNoncentralEigenvalue M)
    (fun i => ae_of_all _ (complexNoncentralSampleEigenvalue_nonneg M i)) r hr
  change (∫ z, actualNoncentralGramLogDet M r z ∂stdGaussian _) ≤ _ at h
  have he : actualNoncentralGramLogDet M r = actualNoncentralMatrixLogDet M r :=
    funext (actualNoncentralGramLogDet_eq_matrix M r hr)
  rw [he,sum_integral_actualNoncentralEigenvalues_eq_power M] at h
  simpa only [Fintype.card_fin] using h

theorem actualNoncentralMatrixLogDet_min_dimension_mean_bound {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (M : Matrix (Fin m) (Fin n) ℂ) (r : ℝ) (hr : 0 ≤ r) :
    (∫ z, actualNoncentralMatrixLogDet M r z ∂stdGaussian _) ≤
      (min m n : ℕ)*Real.log (1+r*actualExpectedGramPower M/(min m n : ℕ)) := by
  by_cases hnm : n ≤ m
  · simpa only [Nat.min_eq_right hnm] using actualNoncentralMatrixLogDet_column_mean_bound hn M r hr
  · have hmn : m ≤ n := le_of_not_ge hnm
    have h := actualNoncentralMatrixLogDet_column_mean_bound hm Mᵀ r hr
    rw [← expected_actualNoncentralMatrixLogDet_transpose M r,← actualExpectedGramPower_transpose M] at h
    simpa only [Nat.min_eq_left hmn] using h

end
end JinWishart
#print axioms JinWishart.sum_actualNoncentralEigenvalues_eq_trace
#print axioms JinWishart.sum_integral_actualNoncentralEigenvalues_eq_power
#print axioms JinWishart.actualExpectedGramPower_nonneg
#print axioms JinWishart.actualExpectedGramPower_transpose
#print axioms JinWishart.actualNoncentralMatrixLogDet_column_mean_bound
#print axioms JinWishart.actualNoncentralMatrixLogDet_min_dimension_mean_bound
