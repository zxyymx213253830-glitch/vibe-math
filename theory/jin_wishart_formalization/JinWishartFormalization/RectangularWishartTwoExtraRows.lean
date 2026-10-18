import JinWishartFormalization.CentralWishartShiftedSecondMoment
import JinWishartFormalization.CentralWishartMinimumBridge

/-!
# Actual central (n+2)-by-n minimum: finite mixed-minor polynomial

Codex proof bodies. The polynomial is explicit and finite, using exact proven
overlapping principal-minor moments, not an assumed spectral density.
[需人工审查] Actual cone/density/model correspondence and complex variance1.
No equality to the original GENERAL T1 determinant candidate is asserted.
-/
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal ComplexOrder
namespace JinWishart
noncomputable section

def twoExtraRowMinimumPolynomial (n : ℕ) (x : ℝ) : ℝ :=
  (((Nat.factorial n : ℕ) : ℝ) * ((Nat.factorial (n+1) : ℕ) : ℝ))⁻¹ *
    ∑ S : Finset (Fin n), ∑ T : Finset (Fin n),
      x^(n-S.card+(n-T.card)) * centralMixedMinorMoment n S T 1 1

theorem twoExtraRowMinimumPolynomial_nonneg (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ twoExtraRowMinimumPolynomial n x := by
  unfold twoExtraRowMinimumPolynomial
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro S _
  apply Finset.sum_nonneg
  intro T _
  exact mul_nonneg (pow_nonneg hx _) (centralMixedMinorMoment_pos _ _ _ _ _).le

theorem ofReal_twoExtraRowPolynomial_sum (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    ENNReal.ofReal (∑ S : Finset (Fin n), ∑ T : Finset (Fin n),
      x^(n-S.card+(n-T.card)) * centralMixedMinorMoment n S T 1 1) =
      ∑ S : Finset (Fin n), ∑ T : Finset (Fin n),
        ENNReal.ofReal (x^(n-S.card+(n-T.card))) *
          ENNReal.ofReal (centralMixedMinorMoment n S T 1 1) := by
  classical
  have hn (S T : Finset (Fin n)) :
      0 ≤ x^(n-S.card+(n-T.card)) * centralMixedMinorMoment n S T 1 1 :=
    mul_nonneg (pow_nonneg hx _) (centralMixedMinorMoment_pos _ _ _ _ _).le
  rw [ENNReal.ofReal_sum_of_nonneg (fun S _ => Finset.sum_nonneg (fun T _ => hn S T))]
  apply Finset.sum_congr rfl
  intro S _
  rw [ENNReal.ofReal_sum_of_nonneg (fun T _ => hn S T)]
  apply Finset.sum_congr rfl
  intro T _
  exact ENNReal.ofReal_mul (pow_nonneg hx _)

theorem actualCentralSquare_shiftedDeterminant_second_normalized_mean
    (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    ENNReal.ofReal ((((Nat.factorial n : ℕ) : ℝ) * ((Nat.factorial (n+1) : ℕ) : ℝ))⁻¹) *
      (∫⁻ A, ENNReal.ofReal ((A+(x : ℂ) • 1).det.re^2)
        ∂complexWishart (m := n) (n := n)) =
      ENNReal.ofReal (twoExtraRowMinimumPolynomial n x) := by
  rw [actualCentralSquare_shiftedDeterminant_second_mean n x hx,
    twoExtraRowMinimumPolynomial,ENNReal.ofReal_mul (by positivity),
    ofReal_twoExtraRowPolynomial_sum n x hx]

theorem actualTwoExtraRows_shiftedCone_probability (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    ((complexWishart (m := n+2) (n := n)).map realCoordinatesOfHermitian)
      (centralCoordinateShiftedCone n x) =
      ENNReal.ofReal (Real.exp (-(n : ℝ)*x) * twoExtraRowMinimumPolynomial n x) := by
  have hp := actualCentralWishart_shiftedCone_probability 2 n x hx
  rw [show 2+n=n+2 by omega] at hp
  have hm := lintegral_complexWishart_eq_cone 0 n
    (fun A => ENNReal.ofReal ((A+(x : ℂ) • 1).det.re^2)) (by fun_prop)
  simp only [Nat.zero_add,centralConeWeight,pow_zero,one_mul] at hm
  simp_rw [ENNReal.ofReal_mul' (Real.exp_nonneg _)] at hp
  rw [centralWishartDensityConstant_two_surplus,div_eq_mul_inv,
    ENNReal.ofReal_mul (centralWishartDensityConstant_pos 0 n).le] at hp
  rw [hp,ENNReal.ofReal_mul (Real.exp_nonneg _)]
  calc
    _ = ENNReal.ofReal (Real.exp (-(n : ℝ)*x)) *
        (ENNReal.ofReal ((((Nat.factorial n : ℕ) : ℝ) * ((Nat.factorial (n+1) : ℕ) : ℝ))⁻¹) *
          (∫⁻ A, ENNReal.ofReal ((A+(x : ℂ) • 1).det.re^2)
            ∂complexWishart (m := n) (n := n))) := by rw [hm]; ring
    _ = _ := by rw [actualCentralSquare_shiftedDeterminant_second_normalized_mean n x hx]

theorem actualTwoExtraRows_minimum_tail (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : 0 ≤ x) :
    (stdGaussian (ComplexSample (m := n+2) (n := n)))
      {z | x < centralGaussianSampleMinimum (n+2) n hn z} =
      ENNReal.ofReal (Real.exp (-(n : ℝ)*x) * twoExtraRowMinimumPolynomial n x) := by
  rw [actualCentralGaussian_minimum_tail_eq_cone,
    actualTwoExtraRows_shiftedCone_probability n x hx]

theorem actualTwoExtraRows_minimum_CDF (n : ℕ) (hn : 0 < n) (x : ℝ) (hx : 0 ≤ x) :
    ((stdGaussian (ComplexSample (m := n+2) (n := n)))
      {z | centralGaussianSampleMinimum (n+2) n hn z ≤ x}).toReal =
      1-Real.exp (-(n : ℝ)*x) * twoExtraRowMinimumPolynomial n x := by
  rw [actualCentralGaussian_minimum_CDF_eq_one_sub_tail,
    actualTwoExtraRows_minimum_tail n hn x hx,
    ENNReal.toReal_ofReal (mul_nonneg (Real.exp_nonneg _) (twoExtraRowMinimumPolynomial_nonneg n x hx))]

theorem actualTwoExtraRows_minimum_cdf_function (n : ℕ) (hn : 0 < n) (x : ℝ) :
    cdf ((stdGaussian (ComplexSample (m := n+2) (n := n))).map
      (centralGaussianSampleMinimum (n+2) n hn)) x =
      if 0 ≤ x then 1-Real.exp (-(n : ℝ)*x) * twoExtraRowMinimumPolynomial n x else 0 := by
  rw [actualCentralGaussian_minimum_cdf_eq_event]
  by_cases hx : 0 ≤ x
  · rw [if_pos hx]
    exact actualTwoExtraRows_minimum_CDF n hn x hx
  · rw [if_neg hx]
    have he : {z : ComplexSample (m := n+2) (n := n) |
        centralGaussianSampleMinimum (n+2) n hn z ≤ x} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact not_le_of_gt (lt_of_lt_of_le (lt_of_not_ge hx)
        (centralGaussianSampleMinimum_nonneg (n+2) n hn z)) hz
    simp [he]

theorem actualTwoExtraRows_scaled_minimum_CDF (n : ℕ) (hn : 0 < n)
    (a : ℝ) (ha : 0 < a) (x : ℝ) (hx : 0 ≤ x) :
    ((stdGaussian (ComplexSample (m := n+2) (n := n)))
      {z | centralGaussianSampleMinimum (n+2) n hn (a • z) ≤ x}).toReal =
      1-Real.exp (-(n : ℝ)*(x/a^2)) * twoExtraRowMinimumPolynomial n (x/a^2) := by
  have he : {z : ComplexSample (m := n+2) (n := n) |
      centralGaussianSampleMinimum (n+2) n hn (a • z) ≤ x} =
      {z | centralGaussianSampleMinimum (n+2) n hn z ≤ x/a^2} := by
    ext z
    simp only [Set.mem_setOf_eq,centralGaussianSampleMinimum_scale (n+2) n hn a ha]
    exact (le_div_iff₀' (sq_pos_of_pos ha)).symm
  rw [he]
  exact actualTwoExtraRows_minimum_CDF n hn _ (div_nonneg hx (sq_nonneg a))

theorem actualTwoExtraRows_covariance_minimum_CDF (n : ℕ) (hn : 0 < n)
    (v : ℝ) (hv : 0 < v) (x : ℝ) (hx : 0 ≤ x) :
    ((stdGaussian (ComplexSample (m := n+2) (n := n)))
      {z | centralGaussianSampleMinimum (n+2) n hn (Real.sqrt v • z) ≤ x}).toReal =
      1-Real.exp (-(n : ℝ)*(x/v)) * twoExtraRowMinimumPolynomial n (x/v) := by
  simpa only [Real.sq_sqrt hv.le] using
    actualTwoExtraRows_scaled_minimum_CDF n hn (Real.sqrt v) (Real.sqrt_pos.mpr hv) x hx

end
end JinWishart
#print axioms JinWishart.twoExtraRowMinimumPolynomial_nonneg
#print axioms JinWishart.ofReal_twoExtraRowPolynomial_sum
#print axioms JinWishart.actualCentralSquare_shiftedDeterminant_second_normalized_mean
#print axioms JinWishart.actualTwoExtraRows_shiftedCone_probability
#print axioms JinWishart.actualTwoExtraRows_minimum_tail
#print axioms JinWishart.actualTwoExtraRows_minimum_CDF
#print axioms JinWishart.actualTwoExtraRows_minimum_cdf_function
#print axioms JinWishart.actualTwoExtraRows_scaled_minimum_CDF
#print axioms JinWishart.actualTwoExtraRows_covariance_minimum_CDF
