import JinWishartFormalization.CentralWishartPolynomialIntegral
import JinWishartFormalization.CentralWishartDeterminantBias

/-!
# All central rectangular minimum laws by a finite factorial polynomial functional

Codex proofs. The coefficient rule is explicit MvPolynomial support summation,
with no unevaluated probability integral or unproved high-order moment premise.
This does not identify the original paper's general determinant candidate.
[需人工审查] Cone integration, actual minimum event and variance interpretation.
-/
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace JinWishart
noncomputable section

def centralRectangularMinimumPolynomial (d n : ℕ) (x : ℝ) : ℝ :=
  (centralDeterminantPowerMoment 0 n d)⁻¹ * centralGaussianShiftedDeterminantMoment d n x

theorem centralRectangularMinimumPolynomial_nonneg (d n : ℕ)
    (x : ℝ) (hx : 0 ≤ x) : 0 ≤ centralRectangularMinimumPolynomial d n x :=
  mul_nonneg (inv_nonneg.mpr (centralDeterminantPowerMoment_pos 0 n d).le)
    (centralGaussianShiftedDeterminantMoment_nonneg d n x hx)

theorem centralWishartDensityConstant_eq_square_ratio (d n : ℕ) :
    centralWishartDensityConstant d n =
      centralWishartDensityConstant 0 n * (centralDeterminantPowerMoment 0 n d)⁻¹ := by
  have h := centralWishartDensityConstant_power_bias 0 n d
  simp only [Nat.zero_add] at h
  have hM := (centralDeterminantPowerMoment_pos 0 n d).ne'
  apply (eq_mul_inv_iff_mul_eq₀ hM).mpr
  nlinarith

theorem actualCentralRectangular_shiftedCone_probability (d n : ℕ)
    (x : ℝ) (hx : 0 ≤ x) :
    ((complexWishart (m := d+n) (n := n)).map realCoordinatesOfHermitian)
      (centralCoordinateShiftedCone n x) =
        ENNReal.ofReal (Real.exp (-(n : ℝ)*x) * centralRectangularMinimumPolynomial d n x) := by
  have hp := actualCentralWishart_shiftedCone_probability d n x hx
  have hm := lintegral_complexWishart_eq_cone 0 n
    (fun A => ENNReal.ofReal ((A+(x : ℂ) • 1).det.re^d)) (by fun_prop)
  simp only [Nat.zero_add,centralConeWeight,pow_zero,one_mul] at hm
  simp_rw [ENNReal.ofReal_mul' (Real.exp_nonneg _)] at hp
  rw [centralWishartDensityConstant_eq_square_ratio,
    ENNReal.ofReal_mul (centralWishartDensityConstant_pos 0 n).le] at hp
  rw [hp,ENNReal.ofReal_mul (Real.exp_nonneg _)]
  calc
    _ = ENNReal.ofReal (Real.exp (-(n : ℝ)*x)) *
        (ENNReal.ofReal ((centralDeterminantPowerMoment 0 n d)⁻¹) *
          (∫⁻ A, ENNReal.ofReal ((A+(x : ℂ) • 1).det.re^d)
            ∂complexWishart (m := n) (n := n))) := by rw [hm]; ring
    _ = _ := by
      rw [lintegral_actualCentralSquare_shiftedDeterminant_power d n x hx,
        centralRectangularMinimumPolynomial,
        ENNReal.ofReal_mul (inv_nonneg.mpr (centralDeterminantPowerMoment_pos 0 n d).le)]

theorem actualCentralRectangular_minimum_tail (d n : ℕ) (hn : 0 < n)
    (x : ℝ) (hx : 0 ≤ x) :
    (stdGaussian (ComplexSample (m := d+n) (n := n)))
      {z | x < centralGaussianSampleMinimum (d+n) n hn z} =
        ENNReal.ofReal (Real.exp (-(n : ℝ)*x) * centralRectangularMinimumPolynomial d n x) := by
  rw [actualCentralGaussian_minimum_tail_eq_cone,
    actualCentralRectangular_shiftedCone_probability d n x hx]

theorem actualCentralRectangular_minimum_CDF (d n : ℕ) (hn : 0 < n)
    (x : ℝ) (hx : 0 ≤ x) :
    ((stdGaussian (ComplexSample (m := d+n) (n := n)))
      {z | centralGaussianSampleMinimum (d+n) n hn z ≤ x}).toReal =
        1-Real.exp (-(n : ℝ)*x) * centralRectangularMinimumPolynomial d n x := by
  rw [actualCentralGaussian_minimum_CDF_eq_one_sub_tail,
    actualCentralRectangular_minimum_tail d n hn x hx,
    ENNReal.toReal_ofReal (mul_nonneg (Real.exp_nonneg _)
      (centralRectangularMinimumPolynomial_nonneg d n x hx))]

theorem actualCentralRectangular_minimum_cdf_function (d n : ℕ) (hn : 0 < n) (x : ℝ) :
    cdf ((stdGaussian (ComplexSample (m := d+n) (n := n))).map
      (centralGaussianSampleMinimum (d+n) n hn)) x =
      if 0 ≤ x then 1-Real.exp (-(n : ℝ)*x) * centralRectangularMinimumPolynomial d n x else 0 := by
  rw [actualCentralGaussian_minimum_cdf_eq_event]
  by_cases hx : 0 ≤ x
  · rw [if_pos hx]
    exact actualCentralRectangular_minimum_CDF d n hn x hx
  · rw [if_neg hx]
    have he : {z : ComplexSample (m := d+n) (n := n) |
        centralGaussianSampleMinimum (d+n) n hn z ≤ x} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact not_le_of_gt (lt_of_lt_of_le (lt_of_not_ge hx)
        (centralGaussianSampleMinimum_nonneg (d+n) n hn z)) hz
    simp [he]

theorem actualCentralRectangular_scaled_minimum_CDF (d n : ℕ) (hn : 0 < n)
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : 0 ≤ x) :
    ((stdGaussian (ComplexSample (m := d+n) (n := n)))
      {z | centralGaussianSampleMinimum (d+n) n hn (a • z) ≤ x}).toReal =
      1-Real.exp (-(n : ℝ)*(x/a^2)) * centralRectangularMinimumPolynomial d n (x/a^2) := by
  have he : {z : ComplexSample (m := d+n) (n := n) |
      centralGaussianSampleMinimum (d+n) n hn (a • z) ≤ x} =
      {z | centralGaussianSampleMinimum (d+n) n hn z ≤ x/a^2} := by
    ext z
    simp only [Set.mem_setOf_eq,centralGaussianSampleMinimum_scale (d+n) n hn a ha]
    exact (le_div_iff₀' (sq_pos_of_pos ha)).symm
  rw [he]
  exact actualCentralRectangular_minimum_CDF d n hn _ (div_nonneg hx (sq_nonneg a))

theorem actualCentralRectangular_covariance_minimum_CDF (d n : ℕ) (hn : 0 < n)
    (v : ℝ) (hv : 0 < v) (x : ℝ) (hx : 0 ≤ x) :
    ((stdGaussian (ComplexSample (m := d+n) (n := n)))
      {z | centralGaussianSampleMinimum (d+n) n hn (Real.sqrt v • z) ≤ x}).toReal =
      1-Real.exp (-(n : ℝ)*(x/v)) * centralRectangularMinimumPolynomial d n (x/v) := by
  simpa only [Real.sq_sqrt hv.le] using
    actualCentralRectangular_scaled_minimum_CDF d n hn (Real.sqrt v) (Real.sqrt_pos.mpr hv) x hx

end
end JinWishart
#print axioms JinWishart.centralRectangularMinimumPolynomial_nonneg
#print axioms JinWishart.centralWishartDensityConstant_eq_square_ratio
#print axioms JinWishart.actualCentralRectangular_shiftedCone_probability
#print axioms JinWishart.actualCentralRectangular_minimum_tail
#print axioms JinWishart.actualCentralRectangular_minimum_CDF
#print axioms JinWishart.actualCentralRectangular_minimum_cdf_function
#print axioms JinWishart.actualCentralRectangular_scaled_minimum_CDF
#print axioms JinWishart.actualCentralRectangular_covariance_minimum_CDF
