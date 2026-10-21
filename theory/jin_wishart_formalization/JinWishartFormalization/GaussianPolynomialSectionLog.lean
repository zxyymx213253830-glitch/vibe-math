import JinWishartFormalization.ComplexGaussianPolynomialLog
import Mathlib.MeasureTheory.Integral.Prod

/-! Parameterized one-variable polynomial negative-log sections.
The coefficient log-L1 assumption is EXPLICIT. This is not the unconditional
multivariate polynomial theorem. No measurable choice of roots is used.
Codex. [需人工审查] Product measurability, Fubini/Tonelli and Gaussian normalization.
-/
open MeasureTheory ProbabilityTheory Filter
namespace JinWishart
noncomputable section

theorem integrable_polynomial_section_negativeLog
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (P : α → Polynomial ℂ)
    (hEval : Measurable (fun w : α × ℂ => (P w.1).eval w.2))
    (hCoeff : Integrable (fun a => complexNegativeLog (P a).leadingCoeff) μ)
    (D : ℕ) (hDegree : ∀ᵐ a ∂μ, (P a).natDegree ≤ D) :
    Integrable (fun w : α × ℂ => complexNegativeLog ((P w.1).eval w.2))
      (μ.prod (stdGaussian ℂ)) ∧
    (∫ w : α × ℂ, complexNegativeLog ((P w.1).eval w.2) ∂μ.prod (stdGaussian ℂ)) ≤
      (∫ a, complexNegativeLog (P a).leadingCoeff ∂μ) + (D : ℝ)/4 := by
  let g : α × ℂ → ℝ := fun w => complexNegativeLog ((P w.1).eval w.2)
  have hgm : AEStronglyMeasurable g (μ.prod (stdGaussian ℂ)) :=
    (measurable_const.max (hEval.norm.log.neg)).aestronglyMeasurable
  have hdom : Integrable (fun a => complexNegativeLog (P a).leadingCoeff+(D : ℝ)/4) μ :=
    hCoeff.add (integrable_const _)
  have hpoint (a : α) (ha : (P a).natDegree ≤ D) :
      (∫ z : ℂ, g (a,z) ∂stdGaussian ℂ) ≤
        complexNegativeLog (P a).leadingCoeff+(D : ℝ)/4 := by
    apply (stdGaussian_complex_polynomial_negativeLog (P a)).2.trans
    exact add_le_add le_rfl (div_le_div_of_nonneg_right (by exact_mod_cast ha) (by norm_num))
  have hn (a : α) : (∫ z : ℂ, ‖g (a,z)‖ ∂stdGaussian ℂ) =
      ∫ z : ℂ, g (a,z) ∂stdGaussian ℂ := by
    apply integral_congr_ae
    filter_upwards [] with z
    exact Real.norm_of_nonneg (le_max_left _ _)
  have hinner : Integrable (fun a => ∫ z : ℂ, ‖g (a,z)‖ ∂stdGaussian ℂ) μ := by
    apply hdom.mono' hgm.norm.integral_prod_right'
    filter_upwards [hDegree] with a ha
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun z => norm_nonneg _)),hn]
    exact hpoint a ha
  have hi : Integrable g (μ.prod (stdGaussian ℂ)) := by
    apply (integrable_prod_iff hgm).mpr
    exact ⟨ae_of_all _ (fun a => (stdGaussian_complex_polynomial_negativeLog (P a)).1),hinner⟩
  refine ⟨hi, ?_⟩
  change (∫ w, g w ∂μ.prod (stdGaussian ℂ)) ≤ _
  rw [integral_prod g hi]
  calc
    _ ≤ ∫ a, complexNegativeLog (P a).leadingCoeff+(D : ℝ)/4 ∂μ :=
      integral_mono_ae hi.integral_prod_left hdom (hDegree.mono (fun a ha => hpoint a ha))
    _ = _ := by rw [integral_add hCoeff (integrable_const _)]; simp

end
end JinWishart
#print axioms JinWishart.integrable_polynomial_section_negativeLog
