import JinWishartFormalization.GaussianRadialCDF
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Explicit integer Gamma CDF power bounds at the hard edge

Codex proofs using the actual CDF integral, not an assumed asymptotic.
[需人工审查] Interval integral comparison and probability interpretation.
-/
open MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

theorem gammaNat_integral_power_normalization (d : ℕ) (x : ℝ) :
    (Nat.factorial d : ℝ)⁻¹ * (∫ u in (0 : ℝ)..x, u^d) =
      x^(d+1)/(Nat.factorial (d+1) : ℝ) := by
  rw [integral_pow]
  simp only [zero_pow (Nat.succ_ne_zero d),sub_zero,Nat.factorial_succ,Nat.cast_mul]
  push_cast
  field_simp

theorem cdf_gammaMeasure_nat_power_upper (d : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    cdf (gammaMeasure ((d+1 : ℕ) : ℝ) 1) x ≤ x^(d+1)/(Nat.factorial (d+1) : ℝ) := by
  rw [cdf_gammaMeasure_nat_eq_lowerGamma (d+1) (Nat.succ_pos d) x hx]
  simp only [Nat.add_sub_cancel]
  rw [← gammaNat_integral_power_normalization d x]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply intervalIntegral.integral_mono_on hx
    ((by fun_prop : Continuous (fun u : ℝ => u^d*Real.exp (-u))).intervalIntegrable 0 x)
    ((by fun_prop : Continuous (fun u : ℝ => u^d)).intervalIntegrable 0 x)
  intro u hu
  exact mul_le_of_le_one_right (pow_nonneg hu.1 d) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu.1))

theorem cdf_gammaMeasure_nat_power_lower (d : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    Real.exp (-x)*x^(d+1)/(Nat.factorial (d+1) : ℝ) ≤
      cdf (gammaMeasure ((d+1 : ℕ) : ℝ) 1) x := by
  rw [cdf_gammaMeasure_nat_eq_lowerGamma (d+1) (Nat.succ_pos d) x hx]
  simp only [Nat.add_sub_cancel]
  have h : (∫ u in (0 : ℝ)..x, Real.exp (-x)*u^d) ≤
      ∫ u in (0 : ℝ)..x, u^d*Real.exp (-u) := by
    apply intervalIntegral.integral_mono_on hx
      ((by fun_prop : Continuous (fun u : ℝ => Real.exp (-x)*u^d)).intervalIntegrable 0 x)
      ((by fun_prop : Continuous (fun u : ℝ => u^d*Real.exp (-u))).intervalIntegrable 0 x)
    intro u hu
    calc
      _ ≤ Real.exp (-u)*u^d := mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (neg_le_neg hu.2)) (pow_nonneg hu.1 d)
      _ = _ := mul_comm _ _
  rw [intervalIntegral.integral_const_mul] at h
  have hm := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (Nat.factorial d : ℝ)⁻¹)
  rw [← mul_assoc, mul_comm (Nat.factorial d : ℝ)⁻¹ (Real.exp (-x)),mul_assoc,
    gammaNat_integral_power_normalization] at hm
  simpa only [mul_div_assoc] using hm

end
end JinWishart
#print axioms JinWishart.gammaNat_integral_power_normalization
#print axioms JinWishart.cdf_gammaMeasure_nat_power_upper
#print axioms JinWishart.cdf_gammaMeasure_nat_power_lower
