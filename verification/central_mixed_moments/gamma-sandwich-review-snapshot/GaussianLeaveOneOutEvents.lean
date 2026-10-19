import JinWishartFormalization.GaussianLeaveOneOutLaw
import JinWishartFormalization.CentralWishartMinimumBridge

/-!
# Actual Gaussian almost-everywhere leave-one-out event inclusions

Codex proofs. Full-rank exceptions are discharged by the actual preceding
Gaussian submatrix law, not assumed away.
[需人工审查] AE transport, finite intersection and event interpretation.
-/
open Matrix MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

theorem gramSmallestValue_sample_eq {m n : ℕ}
    (z : ComplexSample (m := m) (n := n)) (hn : 0 < n) :
    gramSmallestValue (complexSampleMatrix z) hn = centralGaussianSampleMinimum m n hn z := by
  simp only [gramSmallestValue,centralGaussianSampleMinimum,complexNoncentralSampleSmallestEigenvalue,add_zero]

theorem leaveOneOut_preceding_isUnit_ae {m n : ℕ} (hnm : n ≤ m) (j : Fin (n+1)) :
    ∀ᵐ z ∂stdGaussian (ComplexSample (m := m) (n := n+1)),
      IsUnit (complexGram ((complexSampleMatrix z).submatrix id j.succAbove)).det := by
  have hf := complexSample_shiftedGram_isUnit_det_ae (m := m) (n := n) hnm
    (0 : Matrix (Fin m) (Fin n) ℂ)
  simp only [add_zero] at hf
  have hM : Measurable (complexSampleMatrix (m := m) (n := n)) := by
    simpa only [add_zero] using measurable_shiftedComplexSampleMatrix (0 : Matrix (Fin m) (Fin n) ℂ)
  have hset : MeasurableSet {y : ComplexSample (m := m) (n := n) |
      IsUnit (complexGram (complexSampleMatrix y)).det} :=
    (measurableSet_gram_det_isUnit m n).preimage hM
  rw [← stdGaussian_sampleColumnSelection_law (m := m) j.succAbove j.succAbove_right_injective] at hf
  have h := (ae_map_iff (measurable_sampleColumnSelection j.succAbove).aemeasurable hset).mp hf
  simpa only [complexSampleMatrix_columnSelection] using h

theorem totalLeaveOneOutEnergy_eq_residual_ae {m n : ℕ} (hnm : n ≤ m) (j : Fin (n+1)) :
    ∀ᵐ z ∂stdGaussian (ComplexSample (m := m) (n := n+1)),
      totalLeaveOneOutEnergy j z = leaveOneOutResidualEnergy (complexSampleMatrix z) j := by
  filter_upwards [leaveOneOut_preceding_isUnit_ae hnm j] with z hz
  exact totalColumnResidualEnergy_eq_complex_residual _ hz _

theorem actualLeaveOneOut_minimum_le_energy_ae {m n : ℕ} (hnm : n ≤ m) (j : Fin (n+1)) :
    ∀ᵐ z ∂stdGaussian (ComplexSample (m := m) (n := n+1)),
      centralGaussianSampleMinimum m (n+1) (Nat.succ_pos n) z ≤ totalLeaveOneOutEnergy j z := by
  filter_upwards [totalLeaveOneOutEnergy_eq_residual_ae hnm j] with z hz
  rw [hz,← gramSmallestValue_sample_eq]
  exact gramSmallestValue_le_leaveOneOut_energy _ j

theorem actualLeaveOneOut_exists_energy_le_dimension_minimum_ae {m n : ℕ} (hnm : n ≤ m) :
    ∀ᵐ z ∂stdGaussian (ComplexSample (m := m) (n := n+1)),
      ∃ j : Fin (n+1), totalLeaveOneOutEnergy j z ≤
        ((n+1 : ℕ) : ℝ)*centralGaussianSampleMinimum m (n+1) (Nat.succ_pos n) z := by
  have hall : ∀ᵐ z ∂stdGaussian (ComplexSample (m := m) (n := n+1)),
      ∀ j : Fin (n+1), totalLeaveOneOutEnergy j z =
        leaveOneOutResidualEnergy (complexSampleMatrix z) j :=
    ae_all_iff.mpr (fun j => totalLeaveOneOutEnergy_eq_residual_ae hnm j)
  filter_upwards [hall] with z hz
  obtain ⟨j,hj⟩ := exists_leaveOneOut_energy_le_dimension_mul_minimum (complexSampleMatrix z)
  exact ⟨j,by simpa only [hz j,gramSmallestValue_sample_eq] using hj⟩

end
end JinWishart
#print axioms JinWishart.gramSmallestValue_sample_eq
#print axioms JinWishart.leaveOneOut_preceding_isUnit_ae
#print axioms JinWishart.totalLeaveOneOutEnergy_eq_residual_ae
#print axioms JinWishart.actualLeaveOneOut_minimum_le_energy_ae
#print axioms JinWishart.actualLeaveOneOut_exists_energy_le_dimension_minimum_ae
