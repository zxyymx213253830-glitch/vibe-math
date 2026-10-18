import JinWishartFormalization.GammaIntegerMoments
import JinWishartFormalization.CentralWishartDeterminantProduct

/-!
# Actual determinant integer moments, all central full-rank shapes

Codex proof bodies, following the principal-minor route discussed with Qoder.
[需人工审查] Nonnegative Tonelli/product laws and actual determinant convention.
-/
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace JinWishart
noncomputable section

instance isProbabilityMeasure_centralBartlettGammaProductLaw (d n : ℕ) :
    IsProbabilityMeasure (centralBartlettGammaProductLaw d n) := by
  rw [← complexWishart_det_eq_gammaProduct]
  infer_instance

theorem lintegral_centralBartlettGammaProduct_norm_power (d n p : ℕ) :
    ∫⁻ z, ENNReal.ofReal (‖z‖ ^ p) ∂centralBartlettGammaProductLaw d n =
      ∏ j : Fin n, ENNReal.ofReal
        (((Nat.factorial (d + j.val + p) : ℕ) : ℝ) / ((Nat.factorial (d + j.val) : ℕ) : ℝ)) := by
  induction n with
  | zero => simp [centralBartlettGammaProductLaw_zero]
  | succ n ih =>
      rw [centralBartlettGammaProductLaw_succ, lintegral_map (by fun_prop) (by fun_prop)]
      have hf : (fun q : ℝ × ℂ => ENNReal.ofReal (‖(q.1 : ℂ) * q.2‖ ^ p)) =
          (fun q => ENNReal.ofReal (|q.1| ^ p) * ENNReal.ofReal (‖q.2‖ ^ p)) := by
        funext q
        rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
          ENNReal.ofReal_mul (by positivity)]
      change ∫⁻ q : ℝ × ℂ, ENNReal.ofReal (‖(q.1 : ℂ) * q.2‖ ^ p)
        ∂(gammaMeasure ((d + n + 1 : ℕ) : ℝ) 1).prod (centralBartlettGammaProductLaw d n) = _
      rw [hf, lintegral_prod_mul (f := fun r : ℝ => ENNReal.ofReal (|r| ^ p))
        (g := fun z : ℂ => ENNReal.ofReal (‖z‖ ^ p)) (by fun_prop) (by fun_prop),
        lintegral_gammaMeasure_nat_abs_power, ih, Fin.prod_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [mul_comm]

/-- Exact integer absolute determinant moments of the actual Gram distribution. -/
theorem complexWishart_determinant_norm_moment (d n p : ℕ) :
    ∫⁻ W, ENNReal.ofReal (‖W.det‖ ^ p) ∂complexWishart (m := d + n) (n := n) =
      ∏ j : Fin n, ENNReal.ofReal
        (((Nat.factorial (d + j.val + p) : ℕ) : ℝ) / ((Nat.factorial (d + j.val) : ℕ) : ℝ)) := by
  rw [← lintegral_centralBartlettGammaProduct_norm_power d n p,
    ← complexWishart_det_eq_gammaProduct, lintegral_map (by fun_prop) (by fun_prop)]

theorem factorial_ratio_product (d n : ℕ) :
    (∏ j : Fin n, (((Nat.factorial (d + j.val + 1) : ℕ) : ℝ) /
      ((Nat.factorial (d + j.val) : ℕ) : ℝ))) =
      ((Nat.factorial (d + n) : ℕ) : ℝ) / ((Nat.factorial d : ℕ) : ℝ) := by
  induction n with
  | zero => simp [show ((Nat.factorial d : ℕ) : ℝ) ≠ 0 by positivity]
  | succ n ih =>
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih]
      have hd : ((Nat.factorial d : ℕ) : ℝ) ≠ 0 := by positivity
      have hdn : ((Nat.factorial (d + n) : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
      simp only [Nat.add_assoc]

theorem complexWishart_determinant_norm_mean (d n : ℕ) :
    ∫⁻ W, ENNReal.ofReal ‖W.det‖ ∂complexWishart (m := d + n) (n := n) =
      ENNReal.ofReal (((Nat.factorial (d + n) : ℕ) : ℝ) /
        ((Nat.factorial d : ℕ) : ℝ)) := by
  have h := complexWishart_determinant_norm_moment d n 1
  simp only [pow_one] at h
  rw [h, ← ENNReal.ofReal_prod_of_nonneg (fun j _ => by positivity), factorial_ratio_product]

theorem complexWishart_determinant_norm_mean_of_le (t s : ℕ) (hst : s ≤ t) :
    ∫⁻ W, ENNReal.ofReal ‖W.det‖ ∂complexWishart (m := t) (n := s) =
      ENNReal.ofReal (((Nat.factorial t : ℕ) : ℝ) /
        ((Nat.factorial (t - s) : ℕ) : ℝ)) := by
  simpa only [Nat.sub_add_cancel hst] using complexWishart_determinant_norm_mean (t - s) s

end
end JinWishart

#print axioms JinWishart.lintegral_centralBartlettGammaProduct_norm_power
#print axioms JinWishart.isProbabilityMeasure_centralBartlettGammaProductLaw
#print axioms JinWishart.complexWishart_determinant_norm_moment
#print axioms JinWishart.factorial_ratio_product
#print axioms JinWishart.complexWishart_determinant_norm_mean
#print axioms JinWishart.complexWishart_determinant_norm_mean_of_le
