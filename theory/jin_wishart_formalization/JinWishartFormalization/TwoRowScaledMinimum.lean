import JinWishartFormalization.Theorem1CentralTwoRowActualCDF
import JinWishartFormalization.DeepSeekScale20261015.SampleMatrix

/-! Codex actual positive-scale spectral bridge.
[需人工审查] Real scale versus complex variance and paper normalization. -/
open Matrix MeasureTheory ProbabilityTheory
open scoped ComplexOrder ENNReal
namespace JinWishart
noncomputable section

theorem twoRow_posDef_real_smul_iff (A : Matrix (Fin 2) (Fin 2) ℂ)
    (c : ℝ) (hc : 0 < c) : (c • A).PosDef ↔ A.PosDef := by
  constructor
  · intro h
    have hi := h.smul (inv_pos.mpr hc)
    simpa [smul_smul, hc.ne'] using hi
  · intro h
    exact h.smul hc

theorem twoRow_smallest_real_smul (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A.IsHermitian) (c : ℝ) (hc : 0 < c)
    (hB : (c • A).IsHermitian) :
    hB.eigenvalues₀ 1 = c * hA.eigenvalues₀ 1 := by
  apply eq_of_forall_lt_iff
  intro x
  rw [← hermitian_twoRow_shift_posDef_iff_smallest (c • A) hB x]
  have he : c • A - (x : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) =
      c • (A - ((x / c : ℝ) : ℂ) • 1) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Complex.ofReal_div, RCLike.real_smul_eq_coe_mul]
    field_simp [hc.ne']
    <;> simp [mul_comm, mul_left_comm, mul_assoc]
  rw [he, twoRow_posDef_real_smul_iff _ c hc,
    hermitian_twoRow_shift_posDef_iff_smallest A hA (x / c)]
  exact div_lt_iff₀' hc

/-- Gram scaling is proved for actual scaled sample coordinates. -/
theorem twoRow_actualGram_scale (a : ℝ) (z : ComplexSample (m := 2) (n := 2)) :
    complexGram (complexSampleMatrix (a • z)) =
      (a ^ 2) • complexGram (complexSampleMatrix z) := by
  rw [deepseek_scaled_sampleMatrix]
  ext i j
  simp [complexGram, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.smul_apply,
    RCLike.real_smul_eq_coe_mul, smul_eq_mul, Fin.sum_univ_two]
  <;> ring

/-- This is the minimum of the Gram of the scaled sample, not a postulated RV. -/
theorem twoRow_actualMinimum_scale (a : ℝ) (ha : 0 < a)
    (z : ComplexSample (m := 2) (n := 2)) :
    twoRowActualMinimum (a • z) = a ^ 2 * twoRowActualMinimum z := by
  have hi : smallestEigenvalue₀Index (n := 2) (by norm_num) =
      (1 : Fin (Fintype.card (Fin 2))) := by
    apply Fin.ext
    simp [smallestEigenvalue₀Index]
  have hA := (complexGram_posSemidef (complexSampleMatrix z)).1
  have hB : ((a ^ 2) • complexGram (complexSampleMatrix z)).IsHermitian := by
    rw [← twoRow_actualGram_scale]
    exact (complexGram_posSemidef (complexSampleMatrix (a • z))).1
  have h := twoRow_smallest_real_smul _ hA (a ^ 2) (sq_pos_of_pos ha) hB
  simpa only [twoRowActualMinimum, complexNoncentralSampleSmallestEigenvalue,
    add_zero, hi, ← twoRow_actualGram_scale] using h

/-- Actual covariance a^2: strict minimum tail for nonnegative thresholds. -/
theorem actualTwoRow_scaled_minimum_tail (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : 0 ≤ x) :
    (stdGaussian (ComplexSample (m := 2) (n := 2)))
      {z | x < twoRowActualMinimum (a • z)} =
      ENNReal.ofReal (Real.exp (-2 * (x / a ^ 2))) := by
  have he : {z : ComplexSample (m := 2) (n := 2) | x < twoRowActualMinimum (a • z)} =
      {z | x / a ^ 2 < twoRowActualMinimum z} := by
    ext z
    simp only [Set.mem_setOf_eq]
    rw [twoRow_actualMinimum_scale a ha]
    exact (div_lt_iff₀' (sq_pos_of_pos ha)).symm
  rw [he]
  exact actualTwoRow_minimum_tail _ (div_nonneg hx (sq_nonneg a))

theorem actualTwoRow_scaled_minimum_CDF (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : 0 ≤ x) :
    ((stdGaussian (ComplexSample (m := 2) (n := 2)))
      {z | twoRowActualMinimum (a • z) ≤ x}).toReal =
      1 - Real.exp (-2 * (x / a ^ 2)) := by
  have he : {z : ComplexSample (m := 2) (n := 2) | twoRowActualMinimum (a • z) ≤ x} =
      {z | twoRowActualMinimum z ≤ x / a ^ 2} := by
    ext z
    simp only [Set.mem_setOf_eq]
    rw [twoRow_actualMinimum_scale a ha]
    exact (le_div_iff₀' (sq_pos_of_pos ha)).symm
  rw [he]
  exact actualTwoRow_minimum_CDF _ (div_nonneg hx (sq_nonneg a))

/-- The full CDF, including all negative thresholds, for scaled actual samples. -/
theorem actualTwoRow_scaled_minimum_cdf_function (a : ℝ) (ha : 0 < a) (x : ℝ) :
    cdf ((stdGaussian (ComplexSample (m := 2) (n := 2))).map
      (fun z => twoRowActualMinimum (a • z))) x =
      if 0 ≤ x then 1 - Real.exp (-2 * (x / a ^ 2)) else 0 := by
  have hm : Measurable (fun z : ComplexSample (m := 2) (n := 2) =>
      twoRowActualMinimum (a • z)) :=
    measurable_twoRowActualMinimum.comp (measurable_id.const_smul a)
  rw [cdf_eq_real, Measure.real, Measure.map_apply hm measurableSet_Iic]
  change ((stdGaussian (ComplexSample (m := 2) (n := 2)))
    {z | twoRowActualMinimum (a • z) ≤ x}).toReal = _
  by_cases hx : 0 ≤ x
  · rw [if_pos hx]
    exact actualTwoRow_scaled_minimum_CDF a ha x hx
  · rw [if_neg hx]
    have he : {z : ComplexSample (m := 2) (n := 2) |
        twoRowActualMinimum (a • z) ≤ x} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact not_le_of_gt (lt_of_lt_of_le (lt_of_not_ge hx)
        (twoRowActualMinimum_nonneg (a • z))) hz
    simp [he]

/-- Complete actual exponential law with rate 2/a^2. -/
theorem actualTwoRow_scaled_minimum_law (a : ℝ) (ha : 0 < a) :
    (stdGaussian (ComplexSample (m := 2) (n := 2))).map
      (fun z => twoRowActualMinimum (a • z)) = expMeasure (2 / a ^ 2) := by
  have hr : (0 : ℝ) < 2 / a ^ 2 := div_pos (by norm_num) (sq_pos_of_pos ha)
  have : IsProbabilityMeasure (expMeasure (2 / a ^ 2)) := isProbabilityMeasure_expMeasure hr
  apply Measure.eq_of_cdf
  apply StieltjesFunction.ext
  intro x
  rw [actualTwoRow_scaled_minimum_cdf_function a ha, cdf_expMeasure_eq hr]
  congr 1
  congr 1
  congr 1
  ring

/-- Variance v uses sqrt(v) on real Gaussian coordinates; no implicit factor two. -/
theorem actualTwoRow_covariance_minimum_CDF (v : ℝ) (hv : 0 < v) (x : ℝ) (hx : 0 ≤ x) :
    ((stdGaussian (ComplexSample (m := 2) (n := 2)))
      {z | twoRowActualMinimum (Real.sqrt v • z) ≤ x}).toReal =
      1 - Real.exp (-2 * (x / v)) := by
  simpa only [Real.sq_sqrt hv.le] using
    actualTwoRow_scaled_minimum_CDF (Real.sqrt v) (Real.sqrt_pos.mpr hv) x hx

/-- The unmodified paper candidate is evaluated at the variance-adjusted threshold. -/
theorem theorem1CentralTwoRow_scaled_candidate_eq_actualCDF
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : 0 ≤ x) :
    theorem1CdfCandidate 2 2 0 (by omega) (by omega)
      (fun j : Fin 0 => Fin.elim0 j) (x / a ^ 2) =
      ((stdGaussian (ComplexSample (m := 2) (n := 2)))
        {z | twoRowActualMinimum (a • z) ≤ x}).toReal := by
  rw [theorem1CentralTwoRow_candidate_eq_expCDF _ (div_nonneg hx (sq_nonneg a)),
    actualTwoRow_scaled_minimum_CDF a ha x hx]

end
end JinWishart
#print axioms JinWishart.twoRow_posDef_real_smul_iff
#print axioms JinWishart.twoRow_smallest_real_smul

#print axioms JinWishart.twoRow_actualGram_scale
#print axioms JinWishart.twoRow_actualMinimum_scale
#print axioms JinWishart.actualTwoRow_scaled_minimum_tail
#print axioms JinWishart.actualTwoRow_scaled_minimum_CDF

#print axioms JinWishart.actualTwoRow_scaled_minimum_cdf_function

#print axioms JinWishart.actualTwoRow_scaled_minimum_law

#print axioms JinWishart.actualTwoRow_covariance_minimum_CDF

#print axioms JinWishart.theorem1CentralTwoRow_scaled_candidate_eq_actualCDF
