import JinWishartFormalization.ComplexGaussianPhaseMoments

/-!
# Exact mixed monomial integrals for an actual variance-one complex Gaussian

Codex proofs. Reuses the already established Exp(1) radial energy law.
[需人工审查] Bochner integrability, transport and complex variance convention.
-/
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace JinWishart
noncomputable section

theorem standardComplexScalarLaw_norm_sq_law :
    standardComplexScalarLaw.map (fun z : ℂ => ‖z‖^2) = gammaMeasure 1 1 := by
  unfold standardComplexScalarLaw
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have he : (fun z : ℂ => ‖z‖^2) ∘ (fun z => (Real.sqrt 2)⁻¹ • z) =
      complexGaussianEnergy := by
    funext z
    simp only [Function.comp_apply,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,
      inv_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),complexGaussianEnergy]
    ring
  rw [he]
  change (stdGaussian ℂ).map complexGaussianEnergy = expMeasure 1
  letI : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure (by norm_num)
  apply Measure.eq_of_cdf
  ext x
  exact cdf_complexGaussianEnergy_eq_expMeasure x

theorem lintegral_standardComplex_norm_even (k : ℕ) :
    (∫⁻ z : ℂ, ENNReal.ofReal (‖z‖^(2*k)) ∂standardComplexScalarLaw) =
      ENNReal.ofReal (Nat.factorial k : ℝ) := by
  have h := congrArg (fun μ => ∫⁻ r : ℝ, ENNReal.ofReal (r^k) ∂μ)
    standardComplexScalarLaw_norm_sq_law
  rw [lintegral_map (by fun_prop) (by fun_prop)] at h
  have hG := lintegral_gammaMeasure_nat_power 0 k
  norm_num only [Nat.zero_add,Nat.factorial_zero,Nat.cast_one,div_one] at hG
  simpa only [Function.comp_apply,← pow_mul,Nat.zero_add,Nat.zero_add,
    Nat.factorial_zero,Nat.cast_one,div_one] using h.trans hG

theorem integrable_standardComplex_norm_even (k : ℕ) :
    Integrable (fun z : ℂ => ‖z‖^(2*k)) standardComplexScalarLaw := by
  apply (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
    (ae_of_all _ (fun z => pow_nonneg (norm_nonneg z) _))).mp
  rw [lintegral_standardComplex_norm_even]
  exact ENNReal.ofReal_ne_top

theorem integrable_standardComplex_norm_pow (k : ℕ) :
    Integrable (fun z : ℂ => ‖z‖^k) standardComplexScalarLaw := by
  have h := (integrable_const (1 : ℝ)).add (integrable_standardComplex_norm_even k)
  apply h.mono' (by fun_prop)
  filter_upwards [] with z
  rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg z) k)]
  by_cases hz : ‖z‖ ≤ 1
  · exact (pow_le_one₀ (norm_nonneg z) hz).trans
      (le_add_of_nonneg_right (pow_nonneg (norm_nonneg z) (2*k)))
  · have hz1 : 1 ≤ ‖z‖ := (lt_of_not_ge hz).le
    exact (pow_le_pow_right₀ hz1 (by omega : k ≤ 2*k)).trans
      (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1))

theorem integrable_complexGaussian_monomial (p q : ℕ) :
    Integrable (fun z : ℂ => z^p * star z^q) standardComplexScalarLaw := by
  apply (integrable_standardComplex_norm_pow (p+q)).mono' (by fun_prop)
  filter_upwards [] with z
  simp only [norm_mul,norm_pow,norm_star,pow_add,le_refl]

theorem integral_standardComplex_norm_even (k : ℕ) :
    (∫ z : ℂ, ‖z‖^(2*k) ∂standardComplexScalarLaw) = (Nat.factorial k : ℝ) := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ (fun z => pow_nonneg (norm_nonneg z) _)) (by fun_prop),
    lintegral_standardComplex_norm_even,ENNReal.toReal_ofReal (by positivity)]

theorem integral_complexGaussian_monomial (p q : ℕ) :
    (∫ z : ℂ, z^p * star z^q ∂standardComplexScalarLaw) =
      if p=q then (Nat.factorial p : ℂ) else 0 := by
  by_cases hpq : p=q
  · subst q
    rw [if_pos rfl]
    have he : (fun z : ℂ => z^p * star z^p) = fun z => ((‖z‖^(2*p) : ℝ) : ℂ) := by
      funext z
      rw [← mul_pow]
      have hz : z * star z = ((‖z‖^2 : ℝ) : ℂ) := by
        convert RCLike.mul_conj z using 1 <;> norm_cast
      rw [hz,← Complex.ofReal_pow,← pow_mul]
    rw [he,integral_complex_ofReal,integral_standardComplex_norm_even]
    norm_cast
  · rw [if_neg hpq]
    exact integral_complexGaussian_monomial_offDiagonal p q hpq

end
end JinWishart
#print axioms JinWishart.standardComplexScalarLaw_norm_sq_law
#print axioms JinWishart.lintegral_standardComplex_norm_even
#print axioms JinWishart.integrable_standardComplex_norm_even
#print axioms JinWishart.integrable_standardComplex_norm_pow
#print axioms JinWishart.integrable_complexGaussian_monomial
#print axioms JinWishart.integral_standardComplex_norm_even
#print axioms JinWishart.integral_complexGaussian_monomial
