import JinWishartFormalization.ProbabilityTailIntegrability
import JinWishartFormalization.PowerTailIntegrability

/-!
# Exact first-moment criterion from two-sided probability tails

Codex. This includes critical exponent1 divergence, not just sufficiency.
[需人工审查] Layercake, bounded-interval integration and moment interpretation.
-/
open Set MeasureTheory
namespace JinWishart
noncomputable section
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]

theorem probabilityTail_integrableOn_near_zero (f : α → ℝ) :
    IntegrableOn (probabilityTail μ f) (Ioc (0 : ℝ) 4) := by
  apply (integrable_const (1 : ℝ)).mono' (measurable_probabilityTail μ f).aestronglyMeasurable
  filter_upwards [] with t
  rw [Real.norm_eq_abs,abs_of_nonneg (probabilityTail_nonneg μ f t)]
  exact probabilityTail_le_one μ f t

theorem integrable_nonneg_iff_probabilityTail_Ioi_four (f : α → ℝ)
    (hf : Measurable f) (hnn : 0 ≤ᵐ[μ] f) :
    Integrable f μ ↔ IntegrableOn (probabilityTail μ f) (Ioi 4) := by
  rw [integrable_nonneg_iff_probabilityTail μ f hf hnn,
    ← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ)≤4),integrableOn_union]
  simp only [probabilityTail_integrableOn_near_zero,true_and]

theorem integrable_nonneg_iff_two_sided_power_tail (f : α → ℝ)
    (hf : Measurable f) (hnn : 0 ≤ᵐ[μ] f) (k : ℕ)
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hb : ∀ t : ℝ, 4 ≤ t → c/t^k ≤ probabilityTail μ f t ∧ probabilityTail μ f t ≤ C/t^k) :
    Integrable f μ ↔ 1<k := by
  rw [integrable_nonneg_iff_probabilityTail_Ioi_four μ f hf hnn]
  have h := integrableOn_powerTail_iff (probabilityTail μ f) (measurable_probabilityTail μ f)
    (fun t _ => probabilityTail_nonneg μ f t) 0 k c C hc hC (by
      intro t ht
      have ht4 : (4 : ℝ)<t := ht
      simpa only [pow_zero,div_eq_mul_inv,one_mul] using hb t ht4.le)
  simpa only [zero_add] using h

end
end JinWishart
#print axioms JinWishart.probabilityTail_integrableOn_near_zero
#print axioms JinWishart.integrable_nonneg_iff_probabilityTail_Ioi_four
#print axioms JinWishart.integrable_nonneg_iff_two_sided_power_tail
