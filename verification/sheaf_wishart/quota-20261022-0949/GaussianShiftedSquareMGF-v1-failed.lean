import Mathlib.Probability.Distributions.Gaussian.Real

/-! Codex. Seed2026102251 controls before source.
[需人工审查] Completed-square integral and density conversion.
Scalar real standard Gaussian, not the general-row radial-law conclusion. -/
open MeasureTheory ProbabilityTheory Real
namespace JinWishart
noncomputable section

private theorem realQuadraticIntegral (b c d : ℝ) (hb : 0<b) :
    (∫ x : ℝ, exp (-b*x^2+c*x+d)) =
      sqrt (pi/b)*exp (d+c^2/(4*b)) := by
  have h (x : ℝ) : exp (-b*x^2+c*x+d) =
      exp (-b*(x-c/(2*b))^2)*exp (d+c^2/(4*b)) := by
    rw [← exp_add]
    congr 1
    field_simp
    <;> ring
  simp_rw [h]
  rw [integral_mul_const, integral_sub_right_eq_self, integral_gaussian]

theorem gaussianReal_integral_exp_shifted_square (u t : ℝ) (ht : t<1) :
    (∫ x : ℝ, exp (t*(x+u)^2/2) ∂gaussianReal 0 1) =
      (sqrt (1-t))⁻¹ * exp (u^2*t/(2*(1-t))) := by
  have hp : 0<1-t := sub_pos.mpr ht
  have hn : 1-t ≠ 0 := ne_of_gt hp
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  simp only [smul_eq_mul]
  have hfun (x : ℝ) : gaussianPDFReal 0 1 x * exp (t*(x+u)^2/2) =
      (sqrt (2*pi))⁻¹ * exp (-((1-t)/2)*x^2+(t*u)*x+t*u^2/2) := by
    simp only [gaussianPDFReal_def]
    norm_num
    rw [mul_assoc, ← exp_add]
    congr 2
    ring
  simp_rw [hfun]
  rw [integral_const_mul, realQuadraticIntegral _ _ _ (half_pos hp)]
  have he : t*u^2/2+(t*u)^2/(4*((1-t)/2)) = u^2*t/(2*(1-t)) := by
    field_simp
    <;> ring
  rw [he]
  have hs : sqrt (pi/((1-t)/2)) = sqrt (2*pi)/sqrt (1-t) := by
    rw [← sqrt_div (by positivity)]
    congr 1
    field_simp
    <;> ring
  rw [hs]
  have hz : sqrt (2*pi) ≠ 0 := ne_of_gt (sqrt_pos.2 (by positivity))
  field_simp

theorem gaussianReal_integrable_exp_shifted_square (u t : ℝ) (ht : t<1) :
    Integrable (fun x : ℝ => exp (t*(x+u)^2/2)) (gaussianReal 0 1) := by
  apply Integrable.of_integral_ne_zero
  rw [gaussianReal_integral_exp_shifted_square u t ht]
  exact ne_of_gt (mul_pos (inv_pos.2 (sqrt_pos.2 (sub_pos.mpr ht))) (exp_pos _))

end
end JinWishart
#print axioms JinWishart.gaussianReal_integral_exp_shifted_square
#print axioms JinWishart.gaussianReal_integrable_exp_shifted_square
