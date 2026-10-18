import JinWishartFormalization.CentralWishartMinimum

/-!
# Actual square minimum at arbitrary positive scalar covariance

Codex generalizes the earlier dimension-two scaling argument. This proof body
does not copy the local DeepSeek two-dimensional sample-matrix tactic script.
Variance v uses amplitude sqrt(v); Exp rate n/v, every n>0.
[需人工审查] Gaussian amplitude versus complex covariance and spectral model.
-/
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal ComplexOrder
namespace JinWishart
noncomputable section

theorem complexSampleMatrix_real_smul {m n : ℕ} (a : ℝ)
    (z : ComplexSample (m := m) (n := n)) :
    complexSampleMatrix (a • z) = (a : ℂ) • complexSampleMatrix z := by
  ext i j
  simp [complexSampleMatrix, PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  ring

theorem complexSampleGram_real_smul {m n : ℕ} (a : ℝ)
    (z : ComplexSample (m := m) (n := n)) :
    complexGram (complexSampleMatrix (a • z)) =
      (a ^ 2) • complexGram (complexSampleMatrix z) := by
  rw [complexSampleMatrix_real_smul]
  simp only [complexGram, Matrix.conjTranspose_smul, RCLike.star_def, Complex.conj_ofReal,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  ext i j
  simp [Matrix.smul_apply, pow_two, RCLike.real_smul_eq_coe_mul, Complex.ofReal_mul]

theorem posDef_real_smul_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (c : ℝ) (hc : 0 < c) : (c • A).PosDef ↔ A.PosDef := by
  constructor
  · intro h
    have hi := h.smul (inv_pos.mpr hc)
    simpa [smul_smul, hc.ne'] using hi
  · intro h
    exact h.smul hc

theorem smallestEigenvalue_real_smul {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (c : ℝ) (hc : 0 < c)
    (hB : (c • A).IsHermitian) :
    hB.eigenvalues₀ (smallestEigenvalue₀Index hn) =
      c * hA.eigenvalues₀ (smallestEigenvalue₀Index hn) := by
  apply eq_of_forall_lt_iff
  intro x
  rw [← hermitian_shift_posDef_iff_smallest (c • A) hB hn x]
  have he : c • A - (x : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) =
      c • (A - ((x / c : ℝ) : ℂ) • 1) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Complex.ofReal_div, RCLike.real_smul_eq_coe_mul]
    field_simp [hc.ne']
    <;> simp [mul_comm, mul_left_comm, mul_assoc]
  rw [he, posDef_real_smul_iff _ c hc,
    hermitian_shift_posDef_iff_smallest A hA hn (x / c)]
  exact div_lt_iff₀' hc

theorem centralSquareSampleMinimum_scale (n : ℕ) (hn : 0 < n) (a : ℝ) (ha : 0 < a)
    (z : ComplexSample (m := n) (n := n)) :
    centralSquareSampleMinimum n hn (a • z) = a ^ 2 * centralSquareSampleMinimum n hn z := by
  have hA := (complexGram_posSemidef (complexSampleMatrix z)).isHermitian
  have hB : ((a ^ 2) • complexGram (complexSampleMatrix z)).IsHermitian := by
    rw [← complexSampleGram_real_smul]
    exact (complexGram_posSemidef (complexSampleMatrix (a • z))).isHermitian
  have h := smallestEigenvalue_real_smul hn _ hA (a ^ 2) (sq_pos_of_pos ha) hB
  simpa only [centralSquareSampleMinimum, complexNoncentralSampleSmallestEigenvalue,
    add_zero, ← complexSampleGram_real_smul] using h

theorem actualCentralSquare_scaled_minimum_tail (n : ℕ) (hn : 0 < n)
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : 0 ≤ x) :
    (stdGaussian (ComplexSample (m := n) (n := n)))
      {z | x < centralSquareSampleMinimum n hn (a • z)} =
        ENNReal.ofReal (Real.exp (-(n : ℝ) * (x / a ^ 2))) := by
  have he : {z : ComplexSample (m := n) (n := n) | x < centralSquareSampleMinimum n hn (a • z)} =
      {z | x / a ^ 2 < centralSquareSampleMinimum n hn z} := by
    ext z
    simp only [Set.mem_setOf_eq, centralSquareSampleMinimum_scale n hn a ha]
    exact (div_lt_iff₀' (sq_pos_of_pos ha)).symm
  rw [he]
  exact actualCentralSquare_minimum_tail n hn _ (div_nonneg hx (sq_nonneg a))

theorem actualCentralSquare_scaled_minimum_CDF (n : ℕ) (hn : 0 < n)
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : 0 ≤ x) :
    ((stdGaussian (ComplexSample (m := n) (n := n)))
      {z | centralSquareSampleMinimum n hn (a • z) ≤ x}).toReal =
        1 - Real.exp (-(n : ℝ) * (x / a ^ 2)) := by
  have he : {z : ComplexSample (m := n) (n := n) | centralSquareSampleMinimum n hn (a • z) ≤ x} =
      {z | centralSquareSampleMinimum n hn z ≤ x / a ^ 2} := by
    ext z
    simp only [Set.mem_setOf_eq, centralSquareSampleMinimum_scale n hn a ha]
    exact (le_div_iff₀' (sq_pos_of_pos ha)).symm
  rw [he]
  exact actualCentralSquare_minimum_CDF n hn _ (div_nonneg hx (sq_nonneg a))

theorem actualCentralSquare_scaled_minimum_cdf_function (n : ℕ) (hn : 0 < n)
    (a : ℝ) (ha : 0 < a) (x : ℝ) :
    cdf ((stdGaussian (ComplexSample (m := n) (n := n))).map
      (fun z => centralSquareSampleMinimum n hn (a • z))) x =
        if 0 ≤ x then 1 - Real.exp (-(n : ℝ) * (x / a ^ 2)) else 0 := by
  have hm : Measurable (fun z : ComplexSample (m := n) (n := n) =>
      centralSquareSampleMinimum n hn (a • z)) :=
    (measurable_centralSquareSampleMinimum n hn).comp (measurable_id.const_smul a)
  rw [cdf_eq_real, Measure.real, Measure.map_apply hm measurableSet_Iic]
  change ((stdGaussian (ComplexSample (m := n) (n := n)))
    {z | centralSquareSampleMinimum n hn (a • z) ≤ x}).toReal = _
  by_cases hx : 0 ≤ x
  · rw [if_pos hx]
    exact actualCentralSquare_scaled_minimum_CDF n hn a ha x hx
  · rw [if_neg hx]
    have he : {z : ComplexSample (m := n) (n := n) |
        centralSquareSampleMinimum n hn (a • z) ≤ x} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact not_le_of_gt (lt_of_lt_of_le (lt_of_not_ge hx)
        (centralSquareSampleMinimum_nonneg n hn (a • z))) hz
    simp [he]

theorem actualCentralSquare_scaled_minimum_law (n : ℕ) (hn : 0 < n) (a : ℝ) (ha : 0 < a) :
    (stdGaussian (ComplexSample (m := n) (n := n))).map
      (fun z => centralSquareSampleMinimum n hn (a • z)) = expMeasure ((n : ℝ) / a ^ 2) := by
  have hr : (0 : ℝ) < (n : ℝ) / a ^ 2 := div_pos (by exact_mod_cast hn) (sq_pos_of_pos ha)
  have : IsProbabilityMeasure (expMeasure ((n : ℝ) / a ^ 2)) := isProbabilityMeasure_expMeasure hr
  apply Measure.eq_of_cdf
  apply StieltjesFunction.ext
  intro x
  rw [actualCentralSquare_scaled_minimum_cdf_function n hn a ha, cdf_expMeasure_eq hr]
  congr 1
  congr 1
  congr 1
  ring

theorem actualCentralSquare_covariance_minimum_law (n : ℕ) (hn : 0 < n) (v : ℝ) (hv : 0 < v) :
    (stdGaussian (ComplexSample (m := n) (n := n))).map
      (fun z => centralSquareSampleMinimum n hn (Real.sqrt v • z)) = expMeasure ((n : ℝ) / v) := by
  simpa only [Real.sq_sqrt hv.le] using
    actualCentralSquare_scaled_minimum_law n hn (Real.sqrt v) (Real.sqrt_pos.mpr hv)

end
end JinWishart

#print axioms JinWishart.complexSampleMatrix_real_smul
#print axioms JinWishart.complexSampleGram_real_smul
#print axioms JinWishart.posDef_real_smul_iff
#print axioms JinWishart.smallestEigenvalue_real_smul
#print axioms JinWishart.centralSquareSampleMinimum_scale
#print axioms JinWishart.actualCentralSquare_scaled_minimum_tail
#print axioms JinWishart.actualCentralSquare_scaled_minimum_CDF
#print axioms JinWishart.actualCentralSquare_scaled_minimum_cdf_function
#print axioms JinWishart.actualCentralSquare_scaled_minimum_law
#print axioms JinWishart.actualCentralSquare_covariance_minimum_law
