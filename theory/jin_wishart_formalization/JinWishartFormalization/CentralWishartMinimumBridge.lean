import JinWishartFormalization.CentralWishartScaledMinimum

/-! Shared actual spectral-event bridge for ALL central rectangular shapes.
Codex. This avoids introducing a new spectral wrapper proof per row surplus.
[需人工审查] Measurable spectral events and complex variance conventions.
-/
open Matrix MeasureTheory ProbabilityTheory
open scoped ComplexOrder
namespace JinWishart
noncomputable section

def centralGaussianSampleMinimum (m n : ℕ) (hn : 0 < n)
    (z : ComplexSample (m := m) (n := n)) : ℝ :=
  complexNoncentralSampleSmallestEigenvalue (0 : Matrix (Fin m) (Fin n) ℂ) hn z

theorem measurable_centralGaussianSampleMinimum (m n : ℕ) (hn : 0 < n) :
    Measurable (centralGaussianSampleMinimum m n hn) :=
  measurable_complexNoncentralSampleSmallestEigenvalue _ _

theorem centralGaussianSampleMinimum_nonneg (m n : ℕ) (hn : 0 < n)
    (z : ComplexSample (m := m) (n := n)) : 0 ≤ centralGaussianSampleMinimum m n hn z :=
  complexNoncentralGram_eigenvalues₀_nonneg _ _ _

theorem centralGaussianSampleMinimum_threshold (m n : ℕ) (hn : 0 < n)
    (z : ComplexSample (m := m) (n := n)) (x : ℝ) :
    realCoordinatesOfHermitian (complexSampleGram z) ∈ centralCoordinateShiftedCone n x ↔
      x < centralGaussianSampleMinimum m n hn z := by
  have hG := (complexGram_posSemidef (complexSampleMatrix z)).isHermitian
  change (hermitianOfRealCoordinates (realCoordinatesOfHermitian
    (complexGram (complexSampleMatrix z))) - (x : ℂ) • 1).PosDef ↔ _
  rw [hermitianOfRealCoordinates_realCoordinates _ hG,
    hermitian_shift_posDef_iff_smallest _ hG hn x]
  simp only [centralGaussianSampleMinimum,complexNoncentralSampleSmallestEigenvalue,add_zero]

theorem actualCentralGaussian_minimum_tail_eq_cone (m n : ℕ) (hn : 0 < n) (x : ℝ) :
    (stdGaussian (ComplexSample (m := m) (n := n)))
      {z | x < centralGaussianSampleMinimum m n hn z} =
      ((complexWishart (m := m) (n := n)).map realCoordinatesOfHermitian)
        (centralCoordinateShiftedCone n x) := by
  rw [complexWishart,
    Measure.map_map continuous_realCoordinatesOfHermitian.measurable measurable_complexSampleGram,
    Measure.map_apply
      (continuous_realCoordinatesOfHermitian.measurable.comp measurable_complexSampleGram)
      (measurableSet_centralCoordinateShiftedCone n x)]
  congr 1
  ext z
  exact (centralGaussianSampleMinimum_threshold m n hn z x).symm

theorem actualCentralGaussian_minimum_CDF_eq_one_sub_tail (m n : ℕ) (hn : 0 < n) (x : ℝ) :
    ((stdGaussian (ComplexSample (m := m) (n := n)))
      {z | centralGaussianSampleMinimum m n hn z ≤ x}).toReal =
      1-((stdGaussian (ComplexSample (m := m) (n := n)))
        {z | x < centralGaussianSampleMinimum m n hn z}).toReal := by
  have hs : MeasurableSet {z | x < centralGaussianSampleMinimum m n hn z} :=
    measurableSet_lt measurable_const (measurable_centralGaussianSampleMinimum m n hn)
  have h := probReal_add_probReal_compl
    (μ := stdGaussian (ComplexSample (m := m) (n := n))) hs
  have he : {z | x < centralGaussianSampleMinimum m n hn z}ᶜ =
      {z | centralGaussianSampleMinimum m n hn z ≤ x} := by ext z; simp
  rw [he] at h
  simp only [Measure.real] at h
  linarith only [h]

theorem actualCentralGaussian_minimum_cdf_eq_event (m n : ℕ) (hn : 0 < n) (x : ℝ) :
    cdf ((stdGaussian (ComplexSample (m := m) (n := n))).map
      (centralGaussianSampleMinimum m n hn)) x =
      ((stdGaussian (ComplexSample (m := m) (n := n)))
        {z | centralGaussianSampleMinimum m n hn z ≤ x}).toReal := by
  rw [cdf_eq_real,Measure.real,
    Measure.map_apply (measurable_centralGaussianSampleMinimum m n hn) measurableSet_Iic]
  rfl

theorem centralGaussianSampleMinimum_scale (m n : ℕ) (hn : 0 < n) (a : ℝ) (ha : 0 < a)
    (z : ComplexSample (m := m) (n := n)) :
    centralGaussianSampleMinimum m n hn (a • z) = a^2 * centralGaussianSampleMinimum m n hn z := by
  have hA := (complexGram_posSemidef (complexSampleMatrix z)).isHermitian
  have hB : ((a^2) • complexGram (complexSampleMatrix z)).IsHermitian := by
    rw [← complexSampleGram_real_smul]
    exact (complexGram_posSemidef (complexSampleMatrix (a • z))).isHermitian
  have h := smallestEigenvalue_real_smul hn _ hA (a^2) (sq_pos_of_pos ha) hB
  simpa only [centralGaussianSampleMinimum,complexNoncentralSampleSmallestEigenvalue,
    add_zero,← complexSampleGram_real_smul] using h

end
end JinWishart
#print axioms JinWishart.measurable_centralGaussianSampleMinimum
#print axioms JinWishart.centralGaussianSampleMinimum_nonneg
#print axioms JinWishart.centralGaussianSampleMinimum_threshold
#print axioms JinWishart.actualCentralGaussian_minimum_tail_eq_cone
#print axioms JinWishart.actualCentralGaussian_minimum_CDF_eq_one_sub_tail
#print axioms JinWishart.actualCentralGaussian_minimum_cdf_eq_event
#print axioms JinWishart.centralGaussianSampleMinimum_scale
