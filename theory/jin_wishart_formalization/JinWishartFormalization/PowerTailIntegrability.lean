import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Two-sided power comparison with an exact critical integrability threshold

Codex. Lower comparison is essential at the critical exponent.
[需人工审查] Restricted Lebesgue integrability interpretation.
-/
open Set MeasureTheory
namespace JinWishart
noncomputable section

theorem integrableOn_positive_sandwich_iff (F g : ℝ → ℝ) (s : Set ℝ)
    (hF : Measurable F) (hg : Measurable g)
    (hFn : ∀ t ∈ s, 0 ≤ F t) (hgn : ∀ t ∈ s, 0 ≤ g t)
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hb : ∀ t ∈ s, c*g t ≤ F t ∧ F t ≤ C*g t) (hs : MeasurableSet s) :
    IntegrableOn F s ↔ IntegrableOn g s := by
  constructor
  · intro h
    apply (h.const_mul c⁻¹).mono' hg.aestronglyMeasurable
    filter_upwards [ae_restrict_mem hs] with t ht
    rw [Real.norm_eq_abs,abs_of_nonneg (hgn t ht)]
    rw [← div_eq_inv_mul]
    apply (le_div_iff₀ hc).mpr
    simpa only [mul_comm] using (hb t ht).1
  · intro h
    apply (h.const_mul C).mono' hF.aestronglyMeasurable
    filter_upwards [ae_restrict_mem hs] with t ht
    rw [Real.norm_eq_abs,abs_of_nonneg (hFn t ht)]
    exact (hb t ht).2

theorem integrableOn_natPowerRatio_iff (q k : ℕ) :
    IntegrableOn (fun t : ℝ => t^q/t^k) (Ioi 4) ↔ q+1<k := by
  have he : EqOn (fun t : ℝ => t^q/t^k) (fun t : ℝ => t^((q : ℝ)-(k : ℝ))) (Ioi 4) := by
    intro t ht
    have ht4 : (4 : ℝ)<t := ht
    dsimp only
    rw [Real.rpow_sub (by linarith : 0 < t),Real.rpow_natCast,Real.rpow_natCast]
  rw [integrableOn_congr_fun he measurableSet_Ioi,integrableOn_Ioi_rpow_iff (by norm_num : (0 : ℝ)<4)]
  constructor
  · intro h
    exact_mod_cast (by linarith : (q : ℝ)+1<(k : ℝ))
  · intro h
    have hr : (q : ℝ)+1<(k : ℝ) := by exact_mod_cast h
    linarith

theorem integrableOn_powerTail_iff (F : ℝ → ℝ) (hF : Measurable F)
    (hFn : ∀ t ∈ Ioi (4 : ℝ), 0 ≤ F t) (q k : ℕ)
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hb : ∀ t ∈ Ioi (4 : ℝ), c*(t^q/t^k) ≤ F t ∧ F t ≤ C*(t^q/t^k)) :
    IntegrableOn F (Ioi 4) ↔ q+1<k := by
  rw [integrableOn_positive_sandwich_iff F (fun t : ℝ => t^q/t^k) (Ioi 4)
    hF (by fun_prop) hFn (by
      intro t ht
      have ht4 : (4 : ℝ)<t := ht
      have ht0 : 0<t := by linarith
      exact div_nonneg (pow_nonneg ht0.le q) (pow_nonneg ht0.le k))
    c C hc hC hb measurableSet_Ioi]
  exact integrableOn_natPowerRatio_iff q k

end
end JinWishart
#print axioms JinWishart.integrableOn_positive_sandwich_iff
#print axioms JinWishart.integrableOn_natPowerRatio_iff
#print axioms JinWishart.integrableOn_powerTail_iff
