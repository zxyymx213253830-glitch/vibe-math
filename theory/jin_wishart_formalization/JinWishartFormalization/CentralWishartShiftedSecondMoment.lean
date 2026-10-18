import JinWishartFormalization.CentralWishartMixedMinorMoments
import JinWishartFormalization.CentralWishartShiftedDeterminantMean

/-!
# Actual square-law second moment of the shifted determinant

Codex proof bodies. Finite principal-minor products use the actual joint moments.
[需人工审查] Nonnegative product integration and density normalization.
-/
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal ComplexOrder
namespace JinWishart
noncomputable section

theorem centralDeterminantPowerMoment_add (d n p q : ℕ) :
    centralDeterminantPowerMoment d n (p+q) =
      centralDeterminantPowerMoment d n p * centralDeterminantPowerMoment (d+p) n q := by
  unfold centralDeterminantPowerMoment
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  simp only [Nat.add_assoc, Nat.add_right_comm d p j.val]
  have h0 : ((Nat.factorial (d+j.val) : ℕ) : ℝ) ≠ 0 := by positivity
  have h1 : ((Nat.factorial (d+j.val+p) : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

theorem centralDeterminantPowerMoment_one (d n : ℕ) :
    centralDeterminantPowerMoment d n 1 =
      ((Nat.factorial (d+n) : ℕ) : ℝ) / ((Nat.factorial d : ℕ) : ℝ) :=
  factorial_ratio_product d n

theorem centralDeterminantPowerMoment_zero_two (n : ℕ) :
    centralDeterminantPowerMoment 0 n 2 =
      ((Nat.factorial n : ℕ) : ℝ) * ((Nat.factorial (n+1) : ℕ) : ℝ) := by
  rw [show 2=1+1 by rfl, centralDeterminantPowerMoment_add,
    centralDeterminantPowerMoment_one, centralDeterminantPowerMoment_one]
  simp [Nat.add_comm]

theorem centralWishartDensityConstant_two_surplus (n : ℕ) :
    centralWishartDensityConstant 2 n = centralWishartDensityConstant 0 n /
      (((Nat.factorial n : ℕ) : ℝ) * ((Nat.factorial (n+1) : ℕ) : ℝ)) := by
  have h := centralWishartDensityConstant_power_bias 0 n 2
  rw [centralDeterminantPowerMoment_zero_two] at h
  apply (eq_div_iff (by positivity)).mpr
  simpa only [Nat.zero_add, mul_comm] using h.symm

theorem ofReal_shifted_det_square_eq_minor_pairs {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef) (x : ℝ) (hx : 0 ≤ x) :
    ENNReal.ofReal ((A+(x : ℂ) • 1).det.re^2) =
      ∑ S : Finset (Fin n), ∑ T : Finset (Fin n),
        ENNReal.ofReal (x^(n-S.card+(n-T.card))) *
          (ENNReal.ofReal (A.submatrix (Subtype.val : S → Fin n) Subtype.val).det.re *
            ENNReal.ofReal (A.submatrix (Subtype.val : T → Fin n) Subtype.val).det.re) := by
  classical
  have hI : ((x : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (by exact_mod_cast hx)
  have hD : 0 ≤ (A+(x : ℂ) • 1).det.re :=
    (Complex.nonneg_iff.mp (hA.add hI).det_nonneg).1
  rw [ENNReal.ofReal_pow hD, pow_two]
  simp_rw [ofReal_det_add_scalar_eq_sum_principalMinors A hA x hx]
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  apply Finset.sum_congr rfl
  intro T _
  rw [pow_add, ENNReal.ofReal_mul (pow_nonneg hx _)]
  ring

theorem actualCentralSquare_shiftedDeterminant_second_mean (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (∫⁻ A, ENNReal.ofReal ((A+(x : ℂ) • 1).det.re^2)
      ∂complexWishart (m := n) (n := n)) =
      ∑ S : Finset (Fin n), ∑ T : Finset (Fin n),
        ENNReal.ofReal (x^(n-S.card+(n-T.card))) *
          ENNReal.ofReal (centralMixedMinorMoment n S T 1 1) := by
  classical
  have hP : ∀ᵐ W ∂complexWishart (m := n) (n := n), W.PosSemidef :=
    (mem_ae_iff_prob_eq_one Matrix.posSemidef_is_closed.measurableSet).mpr
      complexWishart_measure_posSemidef
  have he : (∫⁻ A, ENNReal.ofReal ((A+(x : ℂ) • 1).det.re^2)
      ∂complexWishart (m := n) (n := n)) =
      ∫⁻ A, ∑ S : Finset (Fin n), ∑ T : Finset (Fin n),
        ENNReal.ofReal (x^(n-S.card+(n-T.card))) *
          (ENNReal.ofReal (A.submatrix (Subtype.val : S → Fin n) Subtype.val).det.re *
            ENNReal.ofReal (A.submatrix (Subtype.val : T → Fin n) Subtype.val).det.re)
        ∂complexWishart (m := n) (n := n) := by
    apply lintegral_congr_ae
    filter_upwards [hP] with A hA
    exact ofReal_shifted_det_square_eq_minor_pairs A hA x hx
  rw [he,lintegral_finsetSum _ (by intro S _; fun_prop)]
  apply Finset.sum_congr rfl
  intro S _
  rw [lintegral_finsetSum _ (by intro T _; fun_prop)]
  apply Finset.sum_congr rfl
  intro T _
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  simpa only [pow_one] using complexWishart_principalMinor_joint_re_moment n n (le_refl n) S T 1 1

end
end JinWishart
#print axioms JinWishart.centralDeterminantPowerMoment_add
#print axioms JinWishart.centralDeterminantPowerMoment_one
#print axioms JinWishart.centralDeterminantPowerMoment_zero_two
#print axioms JinWishart.centralWishartDensityConstant_two_surplus
#print axioms JinWishart.ofReal_shifted_det_square_eq_minor_pairs
#print axioms JinWishart.actualCentralSquare_shiftedDeterminant_second_mean
