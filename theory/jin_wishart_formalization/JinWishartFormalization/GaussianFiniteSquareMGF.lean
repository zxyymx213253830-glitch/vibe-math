import JinWishartFormalization.GaussianShiftedSquareMGF
import Mathlib.MeasureTheory.Integral.Pi

/-! Codex. Seed2026102251 finite-product controls precede source.
[需人工审查] Product Gaussian/Fubini and finite-dimensional model transport.
Real raw independent coordinates; empty finite index is allowed. -/
open MeasureTheory ProbabilityTheory Real
namespace JinWishart
noncomputable section

theorem gaussianPi_integral_exp_shifted_square_sum {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (t : ℝ) (ht : t<1) :
    (∫ x : ι → ℝ, exp (t*(∑ i,(x i+u i)^2)/2)
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
    ((sqrt (1-t))⁻¹)^Fintype.card ι * exp ((∑ i,(u i)^2)*t/(2*(1-t))) := by
  have hfun (x : ι → ℝ) : exp (t*(∑ i,(x i+u i)^2)/2) =
      ∏ i,exp (t*(x i+u i)^2/2) := by
    rw [← exp_sum]
    congr 1
    rw [Finset.mul_sum, Finset.sum_div]
  simp_rw [hfun]
  rw [integral_fintype_prod_eq_prod (fun i x => exp (t*(x+u i)^2/2))]
  simp_rw [gaussianReal_integral_exp_shifted_square _ t ht]
  rw [Finset.prod_mul_distrib, Finset.prod_const, ← exp_sum]
  congr 2
  rw [← Finset.sum_div, ← Finset.sum_mul]

theorem gaussianPi_integrable_exp_shifted_square_sum {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (t : ℝ) (ht : t<1) :
    Integrable (fun x : ι → ℝ => exp (t*(∑ i,(x i+u i)^2)/2))
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  apply Integrable.of_integral_ne_zero
  rw [gaussianPi_integral_exp_shifted_square_sum u t ht]
  apply ne_of_gt
  exact mul_pos (pow_pos (inv_pos.2 (sqrt_pos.2 (sub_pos.mpr ht))) _) (exp_pos _)

end
end JinWishart
#print axioms JinWishart.gaussianPi_integral_exp_shifted_square_sum
#print axioms JinWishart.gaussianPi_integrable_exp_shifted_square_sum
