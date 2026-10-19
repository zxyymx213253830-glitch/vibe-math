import JinWishartFormalization.GaussianLeaveOneOutEvents

/-!
# Actual Gaussian minimum CDF bounded by leave-one-out Gamma marginals

Codex proofs. Only marginal laws and a union bound are used; no independence
between residuals is needed. [需人工审查] AE event/measure interpretation.
This gives a sandwich, not the exact general hard-edge prefactor.
-/
open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace JinWishart
noncomputable section

theorem actualLeaveOneOut_energy_CDF {m n : ℕ} (hn : 0 < n) (hnm : n < m)
    (j : Fin (n+1)) (x : ℝ) :
    (stdGaussian (ComplexSample (m := m) (n := n+1))).real {z | totalLeaveOneOutEnergy j z ≤ x} =
      cdf (gammaMeasure ((m-n : ℕ) : ℝ) 1) x := by
  letI : IsProbabilityMeasure (gammaMeasure ((m-n : ℕ) : ℝ) 1) :=
    isProbabilityMeasure_gammaMeasure (by exact_mod_cast Nat.sub_pos_of_lt hnm) (by norm_num)
  rw [cdf_eq_real,← actualLeaveOneOut_energy_law hn hnm j]
  change ((stdGaussian (ComplexSample (m := m) (n := n+1)))
    {z | totalLeaveOneOutEnergy j z ≤ x}).toReal =
      (((stdGaussian (ComplexSample (m := m) (n := n+1))).map
        (totalLeaveOneOutEnergy j)) (Set.Iic x)).toReal
  rw [Measure.map_apply (measurable_totalLeaveOneOutEnergy j) measurableSet_Iic]
  rfl

theorem actualGaussian_minimum_gamma_lower {m n : ℕ} (hn : 0 < n) (hnm : n < m) (x : ℝ) :
    cdf (gammaMeasure ((m-n : ℕ) : ℝ) 1) x ≤
      (stdGaussian (ComplexSample (m := m) (n := n+1))).real
        {z | centralGaussianSampleMinimum m (n+1) (Nat.succ_pos n) z ≤ x} := by
  rw [← actualLeaveOneOut_energy_CDF hn hnm (0 : Fin (n+1)) x]
  apply ENNReal.toReal_mono (by finiteness)
  apply measure_mono_ae
  filter_upwards [actualLeaveOneOut_minimum_le_energy_ae hnm.le (0 : Fin (n+1))] with z hz
  exact fun h => hz.trans h

theorem actualGaussian_minimum_gamma_upper {m n : ℕ} (hn : 0 < n) (hnm : n < m) (x : ℝ) :
    (stdGaussian (ComplexSample (m := m) (n := n+1))).real
        {z | centralGaussianSampleMinimum m (n+1) (Nat.succ_pos n) z ≤ x} ≤
      ((n+1 : ℕ) : ℝ)*cdf (gammaMeasure ((m-n : ℕ) : ℝ) 1) (((n+1 : ℕ) : ℝ)*x) := by
  let μ := stdGaussian (ComplexSample (m := m) (n := n+1))
  let E := fun j : Fin (n+1) => {z : ComplexSample (m := m) (n := n+1) |
    totalLeaveOneOutEnergy j z ≤ ((n+1 : ℕ) : ℝ)*x}
  have hi : μ.real {z | centralGaussianSampleMinimum m (n+1) (Nat.succ_pos n) z ≤ x} ≤
      μ.real (⋃ j, E j) := by
    apply ENNReal.toReal_mono (by finiteness)
    apply measure_mono_ae
    filter_upwards [actualLeaveOneOut_exists_energy_le_dimension_minimum_ae hnm.le] with z hz
    intro hx
    obtain ⟨j,hj⟩ := hz
    exact Set.mem_iUnion.mpr ⟨j,hj.trans (mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg (n+1)))⟩
  have hu := measureReal_iUnion_fintype_le (μ := μ) E
  have hsum : (∑ j, μ.real (E j)) =
      ((n+1 : ℕ) : ℝ)*cdf (gammaMeasure ((m-n : ℕ) : ℝ) 1) (((n+1 : ℕ) : ℝ)*x) := by
    simp only [μ,E,actualLeaveOneOut_energy_CDF hn hnm,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  exact hi.trans (hu.trans_eq hsum)

theorem actualCentral_minimum_gamma_sandwich (d n : ℕ) (hn : 0 < n) (x : ℝ) :
    cdf (gammaMeasure ((d+1 : ℕ) : ℝ) 1) x ≤
      (stdGaussian (ComplexSample (m := d+(n+1)) (n := n+1))).real
        {z | centralGaussianSampleMinimum (d+(n+1)) (n+1) (Nat.succ_pos n) z ≤ x} ∧
    (stdGaussian (ComplexSample (m := d+(n+1)) (n := n+1))).real
        {z | centralGaussianSampleMinimum (d+(n+1)) (n+1) (Nat.succ_pos n) z ≤ x} ≤
      ((n+1 : ℕ) : ℝ)*cdf (gammaMeasure ((d+1 : ℕ) : ℝ) 1) (((n+1 : ℕ) : ℝ)*x) := by
  have hnm : n < d+(n+1) := by omega
  have hshape : d+(n+1)-n=d+1 := by omega
  exact ⟨by simpa only [hshape] using actualGaussian_minimum_gamma_lower hn hnm x,
    by simpa only [hshape] using actualGaussian_minimum_gamma_upper hn hnm x⟩

end
end JinWishart
#print axioms JinWishart.actualLeaveOneOut_energy_CDF
#print axioms JinWishart.actualGaussian_minimum_gamma_lower
#print axioms JinWishart.actualGaussian_minimum_gamma_upper
#print axioms JinWishart.actualCentral_minimum_gamma_sandwich
