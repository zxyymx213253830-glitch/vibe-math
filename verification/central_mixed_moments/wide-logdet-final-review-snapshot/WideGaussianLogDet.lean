import JinWishartFormalization.ActualGramLogDet
import JinWishartFormalization.GramLogDetTranspose
import JinWishartFormalization.GaussianMatrixBlockLaw

/-! Full log-det expectation in both matrix orientations, and prelog min(m,N).
Codex. Transpose of the real source preserves Gaussian and sends mean to M^T.
[需人工审查] Gaussian transport, variance and small-side logdet interpretation.
-/
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace JinWishart
noncomputable section

theorem actualNoncentralMatrixLogDet_transpose {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (r : ℝ) (z : ComplexSample (m := m) (n := n)) :
    actualNoncentralMatrixLogDet M r z =
      actualNoncentralMatrixLogDet Mᵀ r (complexSampleTransposeReindex m n z) := by
  unfold actualNoncentralMatrixLogDet
  rw [complexSampleMatrix_transpose_reindex,← Matrix.transpose_add,
    ← det_one_add_gram_transpose]

theorem expected_actualNoncentralMatrixLogDet_transpose {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (r : ℝ) :
    (∫ z, actualNoncentralMatrixLogDet M r z ∂stdGaussian _) =
      ∫ z, actualNoncentralMatrixLogDet Mᵀ r z ∂stdGaussian _ := by
  let e : ComplexSample (m := m) (n := n) ≃ᵐ ComplexSample (m := n) (n := m) :=
    (complexSampleTransposeReindex m n).toHomeomorph.toMeasurableEquiv
  have hmap : (stdGaussian (ComplexSample (m := m) (n := n))).map e =
      stdGaussian (ComplexSample (m := n) (n := m)) := stdGaussian_map _
  calc
    _ = ∫ z, actualNoncentralMatrixLogDet Mᵀ r (e z) ∂stdGaussian _ :=
      integral_congr_ae (ae_of_all _ (actualNoncentralMatrixLogDet_transpose M r))
    _ = _ := by
      have h := integral_map_equiv (μ := stdGaussian (ComplexSample (m := m) (n := n)))
        e (actualNoncentralMatrixLogDet Mᵀ r)
      rw [hmap] at h
      exact h.symm

theorem actualNoncentralMatrixLogDet_allShapes_prelog {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (M : Matrix (Fin m) (Fin n) ℂ) :
    Tendsto (fun r : ℝ => (∫ z, actualNoncentralMatrixLogDet M r z ∂stdGaussian _)/Real.log r)
      atTop (𝓝 (min m n : ℕ)) := by
  by_cases hnm : n ≤ m
  · simpa only [Nat.min_eq_right hnm] using actualNoncentralMatrixLogDet_expected_prelog hn hnm M
  · have hmn : m ≤ n := (le_of_not_ge hnm)
    rw [Nat.min_eq_left hmn]
    apply (actualNoncentralMatrixLogDet_expected_prelog hm hmn Mᵀ).congr'
    exact Filter.Eventually.of_forall (fun r => by
      dsimp only
      rw [expected_actualNoncentralMatrixLogDet_transpose M r])

theorem integral_actualRowGram_logdet_eq_transpose {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) :
    (∫ z : ComplexSample (m := m) (n := n),
      Real.log (((complexSampleMatrix z+M)*(complexSampleMatrix z+M)ᴴ).det.re) ∂stdGaussian _) =
      ∫ z, Real.log ((complexGram (complexSampleMatrix z+Mᵀ)).det.re) ∂stdGaussian _ := by
  let e : ComplexSample (m := m) (n := n) ≃ᵐ ComplexSample (m := n) (n := m) :=
    (complexSampleTransposeReindex m n).toHomeomorph.toMeasurableEquiv
  have hmap : (stdGaussian (ComplexSample (m := m) (n := n))).map e =
      stdGaussian (ComplexSample (m := n) (n := m)) := stdGaussian_map _
  have he (z : ComplexSample (m := m) (n := n)) :
      Real.log (((complexSampleMatrix z+M)*(complexSampleMatrix z+M)ᴴ).det.re) =
        Real.log ((complexGram (complexSampleMatrix (e z)+Mᵀ)).det.re) := by
    change _ = Real.log ((complexGram (complexSampleMatrix
      (complexSampleTransposeReindex m n z)+Mᵀ)).det.re)
    rw [complexSampleMatrix_transpose_reindex,← Matrix.transpose_add,← det_rowGram_eq_transposeGram]
  calc
    _ = ∫ z, Real.log ((complexGram (complexSampleMatrix (e z)+Mᵀ)).det.re) ∂stdGaussian _ :=
      integral_congr_ae (ae_of_all _ he)
    _ = _ := by
      have h := integral_map_equiv (μ := stdGaussian (ComplexSample (m := m) (n := n)))
        e (fun z => Real.log ((complexGram (complexSampleMatrix z+Mᵀ)).det.re))
      rw [hmap] at h
      exact h.symm

theorem actualNoncentralWideMatrixLogDet_expected_offset {m n : ℕ}
    (hm : 0 < m) (hmn : m ≤ n) (M : Matrix (Fin m) (Fin n) ℂ) :
    Tendsto (fun r : ℝ => (∫ z, actualNoncentralMatrixLogDet M r z ∂stdGaussian _)-
      (m : ℝ)*Real.log r) atTop
      (𝓝 (∫ z : ComplexSample (m := m) (n := n),
        Real.log (((complexSampleMatrix z+M)*(complexSampleMatrix z+M)ᴴ).det.re) ∂stdGaussian _)) := by
  rw [integral_actualRowGram_logdet_eq_transpose M]
  apply (actualNoncentralMatrixLogDet_expected_offset hm hmn Mᵀ).congr'
  exact Filter.Eventually.of_forall (fun r => by
    dsimp only
    rw [expected_actualNoncentralMatrixLogDet_transpose M r])

theorem integrable_actualNoncentral_rowGram_logdet {m n : ℕ}
    (hm : 0 < m) (hmn : m ≤ n) (M : Matrix (Fin m) (Fin n) ℂ) :
    Integrable (fun z : ComplexSample (m := m) (n := n) =>
      Real.log (((complexSampleMatrix z+M)*(complexSampleMatrix z+M)ᴴ).det.re)) (stdGaussian _) := by
  let e : ComplexSample (m := m) (n := n) ≃ᵐ ComplexSample (m := n) (n := m) :=
    (complexSampleTransposeReindex m n).toHomeomorph.toMeasurableEquiv
  have hmap : (stdGaussian (ComplexSample (m := m) (n := n))).map e =
      stdGaussian (ComplexSample (m := n) (n := m)) := stdGaussian_map _
  have hi := integrable_actualNoncentral_logGramDet hm hmn Mᵀ
  rw [← hmap] at hi
  have ht := (integrable_map_measure hi.aestronglyMeasurable e.measurable.aemeasurable).mp hi
  apply ht.congr
  exact ae_of_all _ (fun z => by
    change Real.log ((complexGram (complexSampleMatrix
      (complexSampleTransposeReindex m n z)+Mᵀ)).det.re) = _
    rw [complexSampleMatrix_transpose_reindex,← Matrix.transpose_add,← det_rowGram_eq_transposeGram])

end
end JinWishart
#print axioms JinWishart.actualNoncentralMatrixLogDet_transpose
#print axioms JinWishart.expected_actualNoncentralMatrixLogDet_transpose
#print axioms JinWishart.actualNoncentralMatrixLogDet_allShapes_prelog
#print axioms JinWishart.integral_actualRowGram_logdet_eq_transpose
#print axioms JinWishart.actualNoncentralWideMatrixLogDet_expected_offset
#print axioms JinWishart.integrable_actualNoncentral_rowGram_logdet
