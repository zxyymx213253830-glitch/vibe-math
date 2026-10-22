import JinWishartFormalization.NegativeLogNaturalMomentBounds
import JinWishartFormalization.ComplexGaussianRootNegativeLog

/-! Root-uniform positive natural negative-log moments for planar stdGaussian(C).
Its complex second moment is2, not properCN1. Codex.
[需人工审查] Disk/variance normalization and logarithmic layercake. -/
open MeasureTheory ProbabilityTheory Set
namespace JinWishart
noncomputable section

theorem stdGaussian_complex_squared_distance_smallball (a : ℂ) (x : ℝ) (hx : 0<x) :
    (stdGaussian ℂ).real {z : ℂ | ‖z-a‖^2≤x}≤(1/2)*x := by
  have he : {z : ℂ | ‖z-a‖^2≤x}=Metric.closedBall a (Real.sqrt x) := by
    ext z
    simp only [Set.mem_setOf_eq,Metric.mem_closedBall,dist_eq_norm]
    constructor
    · intro hz
      apply (sq_le_sq₀ (norm_nonneg (z-a)) (Real.sqrt_nonneg x)).mp
      simpa only [Real.sq_sqrt hx.le] using hz
    · intro hz
      have hs := (sq_le_sq₀ (norm_nonneg (z-a)) (Real.sqrt_nonneg x)).mpr hz
      simpa only [Real.sq_sqrt hx.le] using hs
  rw [he]
  have h := stdGaussian_complex_closedBall_le_radius_sq_half a (Real.sqrt x) (Real.sqrt_nonneg x)
  rw [Real.sq_sqrt hx.le] at h
  linarith

theorem stdGaussian_complex_negativeLog_natPower_uniform_root (a : ℂ) (q : ℕ) :
    Integrable (fun z : ℂ => (complexNegativeLog (z-a))^(q+1)) (stdGaussian ℂ) ∧
      (∫ z : ℂ,(complexNegativeLog (z-a))^(q+1) ∂stdGaussian ℂ)≤
        ((q+1).factorial : ℝ)/(2*2^(q+1)) := by
  have hs := negativeLog_natPower_integrable_integral_le_of_smallball (stdGaussian ℂ)
    (fun z : ℂ => ‖z-a‖^2) (by fun_prop) (1/2) (by norm_num)
    (stdGaussian_complex_squared_distance_smallball a) q
  have heq (z : ℂ) : (complexNegativeLog (z-a))^(q+1) =
      (max 0 (-Real.log (‖z-a‖^2)))^(q+1)/(2:ℝ)^(q+1) := by
    have htwice : max 0 (-Real.log (‖z-a‖^2))=2*complexNegativeLog (z-a) := by
      rw [complexNegativeLog,Real.log_pow,mul_max_of_nonneg _ _ (by norm_num : (0:ℝ)≤2)]
      simp only [mul_zero,mul_neg,Nat.cast_ofNat]
    rw [htwice,mul_pow]
    field_simp
  refine ⟨(hs.1.div_const _).congr (ae_of_all _ (fun z => (heq z).symm)),?_⟩
  calc
    _ = (∫ z : ℂ,(max 0 (-Real.log (‖z-a‖^2)))^(q+1) ∂stdGaussian ℂ)/(2:ℝ)^(q+1) := by
      rw [← integral_div]
      exact integral_congr_ae (ae_of_all _ heq)
    _ ≤ ((1/2)*((q+1).factorial : ℝ))/(2:ℝ)^(q+1) :=
      div_le_div_of_nonneg_right hs.2 (by positivity)
    _ = _ := by ring

theorem stdGaussian_complex_negativeLog_sq_uniform_root (a : ℂ) :
    Integrable (fun z : ℂ => (complexNegativeLog (z-a))^2) (stdGaussian ℂ) ∧
      (∫ z : ℂ,(complexNegativeLog (z-a))^2 ∂stdGaussian ℂ)≤1/4 := by
  have h := stdGaussian_complex_negativeLog_natPower_uniform_root a 1
  norm_num at h ⊢
  exact h

end
end JinWishart
#print axioms JinWishart.stdGaussian_complex_squared_distance_smallball
#print axioms JinWishart.stdGaussian_complex_negativeLog_natPower_uniform_root
#print axioms JinWishart.stdGaussian_complex_negativeLog_sq_uniform_root
