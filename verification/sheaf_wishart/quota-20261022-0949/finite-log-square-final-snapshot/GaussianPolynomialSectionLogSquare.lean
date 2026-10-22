import JinWishartFormalization.ComplexGaussianPolynomialLogSquare
import Mathlib.MeasureTheory.Integral.Prod

/-! Negative-log square for parameterized polynomial sections.
Coefficient square-L1 and deterministic degree bound are explicit premises.
No measurable choice of roots. Codex. [需人工审查] Product/Fubini/normalization. -/
open MeasureTheory ProbabilityTheory Filter
namespace JinWishart
noncomputable section

theorem integrable_polynomial_section_negativeLog_sq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (P : α → Polynomial ℂ)
    (hEval : Measurable (fun w : α × ℂ => (P w.1).eval w.2))
    (hCoeff : Integrable (fun a => (complexNegativeLog (P a).leadingCoeff)^2) μ)
    (D : ℕ) (hDegree : ∀ᵐ a ∂μ,(P a).natDegree≤D) :
    Integrable (fun w : α × ℂ => (complexNegativeLog ((P w.1).eval w.2))^2)
      (μ.prod (stdGaussian ℂ)) ∧
    (∫ w : α × ℂ,(complexNegativeLog ((P w.1).eval w.2))^2 ∂μ.prod (stdGaussian ℂ))≤
      2*(∫ a,(complexNegativeLog (P a).leadingCoeff)^2 ∂μ)+(D : ℝ)^2/2 := by
  let g : α × ℂ → ℝ := fun w => (complexNegativeLog ((P w.1).eval w.2))^2
  have hgm : AEStronglyMeasurable g (μ.prod (stdGaussian ℂ)) :=
    ((measurable_const.max hEval.norm.log.neg).pow_const 2).aestronglyMeasurable
  have hdom : Integrable (fun a=>2*(complexNegativeLog (P a).leadingCoeff)^2+(D : ℝ)^2/2) μ :=
    (hCoeff.const_mul 2).add (integrable_const _)
  have hpoint (a : α) (ha : (P a).natDegree≤D) :
      (∫ z : ℂ,g (a,z) ∂stdGaussian ℂ)≤2*(complexNegativeLog (P a).leadingCoeff)^2+(D : ℝ)^2/2 := by
    apply (stdGaussian_complex_polynomial_negativeLog_sq (P a)).2.trans
    apply add_le_add le_rfl
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast ha) 2
  have hn (a : α) : (∫ z : ℂ,‖g (a,z)‖ ∂stdGaussian ℂ)=∫ z : ℂ,g (a,z) ∂stdGaussian ℂ := by
    apply integral_congr_ae
    exact ae_of_all _ (fun z => Real.norm_of_nonneg (sq_nonneg _))
  have hinner : Integrable (fun a=>∫ z : ℂ,‖g (a,z)‖ ∂stdGaussian ℂ) μ := by
    apply hdom.mono' hgm.norm.integral_prod_right'
    filter_upwards [hDegree] with a ha
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun z=>norm_nonneg _)),hn]
    exact hpoint a ha
  have hi : Integrable g (μ.prod (stdGaussian ℂ)) := by
    apply (integrable_prod_iff hgm).mpr
    exact ⟨ae_of_all _ (fun a=>(stdGaussian_complex_polynomial_negativeLog_sq (P a)).1),hinner⟩
  refine ⟨hi,?_⟩
  change (∫ w,g w ∂μ.prod (stdGaussian ℂ))≤_
  rw [integral_prod g hi]
  calc
    _ ≤ ∫ a,2*(complexNegativeLog (P a).leadingCoeff)^2+(D : ℝ)^2/2 ∂μ :=
      integral_mono_ae hi.integral_prod_left hdom (hDegree.mono (fun a ha=>hpoint a ha))
    _ = _ := by rw [integral_add (hCoeff.const_mul _) (integrable_const _)]; simp [integral_const_mul]

end
end JinWishart
#print axioms JinWishart.integrable_polynomial_section_negativeLog_sq
