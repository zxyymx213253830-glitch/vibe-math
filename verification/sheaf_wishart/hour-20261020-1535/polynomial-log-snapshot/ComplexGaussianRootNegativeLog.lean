import JinWishartFormalization.ProbabilityNegativeLogBounds
import JinWishartFormalization.ScalarUniformSmallBall

/-! A root-uniform logarithmic bound for the planar Gaussian with two real
variance-one coordinates. This is stdGaussian(C), not proper CN1.
Codex. [需人工审查] Gaussian/disk normalization and logarithmic expectation.
-/
open MeasureTheory ProbabilityTheory Set
namespace JinWishart
noncomputable section

def complexNegativeLog (z : ℂ) : ℝ := max 0 (-Real.log ‖z‖)

theorem complexNegativeLog_mul_le (a b : ℂ) :
    complexNegativeLog (a*b) ≤ complexNegativeLog a + complexNegativeLog b := by
  by_cases ha : a=0
  · simp [ha,complexNegativeLog]
  by_cases hb : b=0
  · simp [hb,complexNegativeLog]
  have hl : Real.log ‖a*b‖ = Real.log ‖a‖ + Real.log ‖b‖ := by
    rw [norm_mul,Real.log_mul (norm_ne_zero_iff.mpr ha) (norm_ne_zero_iff.mpr hb)]
  unfold complexNegativeLog
  rw [hl]
  apply max_le
  · exact add_nonneg (le_max_left _ _) (le_max_left _ _)
  · have h1 := le_max_right (0 : ℝ) (-Real.log ‖a‖)
    have h2 := le_max_right (0 : ℝ) (-Real.log ‖b‖)
    linarith

theorem stdGaussian_complex_negativeLog_uniform_root (μ : ℂ) :
    Integrable (fun z : ℂ => complexNegativeLog (z-μ)) (stdGaussian ℂ) ∧
      (∫ z : ℂ, complexNegativeLog (z-μ) ∂stdGaussian ℂ) ≤ 1/4 := by
  have hsmall : ∀ x : ℝ, 0 < x →
      (stdGaussian ℂ).real {z : ℂ | ‖z-μ‖^2 ≤ x} ≤ (1/2)*x := by
    intro x hx
    have hset : {z : ℂ | ‖z-μ‖^2 ≤ x} = Metric.closedBall μ (Real.sqrt x) := by
      ext z
      simp only [Set.mem_setOf_eq,Metric.mem_closedBall,dist_eq_norm]
      constructor
      · intro hz
        apply (sq_le_sq₀ (norm_nonneg (z-μ)) (Real.sqrt_nonneg x)).mp
        simpa only [Real.sq_sqrt hx.le] using hz
      · intro hz
        have hsq := (sq_le_sq₀ (norm_nonneg (z-μ)) (Real.sqrt_nonneg x)).mpr hz
        simpa only [Real.sq_sqrt hx.le] using hsq
    rw [hset]
    have h := stdGaussian_complex_closedBall_le_radius_sq_half μ (Real.sqrt x) (Real.sqrt_nonneg x)
    rw [Real.sq_sqrt hx.le] at h
    linarith
  have hs := negativeLog_integrable_integral_le_of_smallball (stdGaussian ℂ)
    (fun z : ℂ => ‖z-μ‖^2) (by fun_prop) (1/2) (by norm_num) hsmall
  have heq (z : ℂ) : complexNegativeLog (z-μ) =
      max 0 (-Real.log (‖z-μ‖^2))/2 := by
    have htwice : max 0 (-Real.log (‖z-μ‖^2)) = 2*complexNegativeLog (z-μ) := by
      rw [complexNegativeLog,Real.log_pow,
        mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
      simp only [mul_zero,mul_neg,Nat.cast_ofNat]
    linarith
  have hi : Integrable (fun z : ℂ => complexNegativeLog (z-μ)) (stdGaussian ℂ) :=
    (hs.1.div_const 2).congr (ae_of_all _ (fun z => (heq z).symm))
  refine ⟨hi, ?_⟩
  calc
    _ = (∫ z : ℂ, max 0 (-Real.log (‖z-μ‖^2)) ∂stdGaussian ℂ)/2 := by
      rw [← integral_div]
      exact integral_congr_ae (ae_of_all _ heq)
    _ ≤ (1/2)/2 := div_le_div_of_nonneg_right hs.2 (by norm_num)
    _ = 1/4 := by norm_num

end
end JinWishart
#print axioms JinWishart.complexNegativeLog_mul_le
#print axioms JinWishart.stdGaussian_complex_negativeLog_uniform_root
