import JinWishartFormalization.GaussianFiniteSquareMGF

/-! Codex. Seed2026102507 nonuniform independent quadrature controls precede source.
[需人工审查] Finite product/Fubini and scalar completed-square dependency.
Independent real coordinates, all finite index types including empty. -/
open MeasureTheory ProbabilityTheory Real
namespace JinWishart
noncomputable section

theorem gaussianPi_integral_exp_weighted_shifted_squares {ι : Type*} [Fintype ι]
    (u t : ι → ℝ) (ht : ∀ i,t i<1) :
    (∫ x : ι → ℝ,exp (∑ i,t i*(x i+u i)^2/2)
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      (∏ i,(sqrt (1-t i))⁻¹)*exp (∑ i,(u i)^2*t i/(2*(1-t i))) := by
  have hfun (x : ι → ℝ) : exp (∑ i,t i*(x i+u i)^2/2)=
      ∏ i,exp (t i*(x i+u i)^2/2) := by rw [exp_sum]
  simp_rw [hfun]
  rw [integral_fintype_prod_eq_prod (fun i x => exp (t i*(x+u i)^2/2))]
  simp_rw [gaussianReal_integral_exp_shifted_square _ _ (ht _)]
  rw [Finset.prod_mul_distrib,← exp_sum]

theorem gaussianPi_integrable_exp_weighted_shifted_squares {ι : Type*} [Fintype ι]
    (u t : ι → ℝ) (ht : ∀ i,t i<1) :
    Integrable (fun x : ι → ℝ => exp (∑ i,t i*(x i+u i)^2/2))
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  apply Integrable.of_integral_ne_zero
  rw [gaussianPi_integral_exp_weighted_shifted_squares u t ht]
  apply ne_of_gt
  apply mul_pos
  · apply Finset.prod_pos
    intro i _
    exact inv_pos.2 (sqrt_pos.2 (sub_pos.mpr (ht i)))
  · exact exp_pos _

end
end JinWishart
#print axioms JinWishart.gaussianPi_integral_exp_weighted_shifted_squares
#print axioms JinWishart.gaussianPi_integrable_exp_weighted_shifted_squares
