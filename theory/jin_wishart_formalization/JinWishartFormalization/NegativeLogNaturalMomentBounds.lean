import JinWishartFormalization.ProbabilityNegativeLogBounds
import JinWishartFormalization.ProbabilityTailNaturalMoments
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-! Every positive natural negative-log moment from a linear small-ball bound.
Codex. [需人工审查] Weighted layercake, Gamma normalization and totalized log0. -/
open MeasureTheory Set Filter
namespace JinWishart
noncomputable section

theorem integral_natPower_exp_neg_Ioi (q : ℕ) :
    IntegrableOn (fun t : ℝ => t^q*Real.exp (-t)) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0,t^q*Real.exp (-t)) = (q.factorial : ℝ) := by
  have hp : 0<(q : ℝ)+1 := by positivity
  constructor
  · simpa [Real.rpow_natCast,mul_comm] using Real.GammaIntegral_convergent hp
  · have h := Real.Gamma_eq_integral hp
    rw [Real.Gamma_nat_eq_factorial] at h
    simpa [Real.rpow_natCast,mul_comm] using h.symm

theorem negativeLog_natPower_integrable_integral_le_of_smallball
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α→ℝ) (hf : Measurable f) (C : ℝ) (hC : 0≤C)
    (hsmall : ∀ x : ℝ,0<x → μ.real {a | f a≤x}≤C*x) (q : ℕ) :
    Integrable (fun a => (max 0 (-Real.log (f a)))^(q+1)) μ ∧
      (∫ a,(max 0 (-Real.log (f a)))^(q+1) ∂μ) ≤ C*((q+1).factorial : ℝ) := by
  let Y : α→ℝ := fun a => max 0 (-Real.log (f a))
  have hYm : Measurable Y := measurable_const.max hf.log.neg
  have hYn : 0≤ᵐ[μ] Y := ae_of_all _ (fun a => le_max_left _ _)
  have hw := measurable_weightedProbabilityTail μ Y q
  have hmajor : IntegrableOn (fun t : ℝ => (((q+1 : ℕ) : ℝ)*C)*(t^q*Real.exp (-t))) (Ioi 0) :=
    (integral_natPower_exp_neg_Ioi q).1.const_mul _
  have hb : ∀ t : ℝ,0<t → weightedProbabilityTail μ Y q t ≤
      (((q+1 : ℕ) : ℝ)*C)*(t^q*Real.exp (-t)) := by
    intro t ht
    have h := mul_le_mul_of_nonneg_left (negativeLog_probabilityTail_le μ f C hsmall t ht)
      (by positivity : 0≤((q+1 : ℕ) : ℝ)*t^q)
    dsimp only [weightedProbabilityTail]
    convert h using 1 <;> ring
  have htail : IntegrableOn (weightedProbabilityTail μ Y q) (Ioi 0) := by
    apply hmajor.mono' hw.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0<t := ht
    have hnn : 0≤weightedProbabilityTail μ Y q t := by
      dsimp only [weightedProbabilityTail]
      exact mul_nonneg (by positivity) (probabilityTail_nonneg μ Y t)
    rw [Real.norm_eq_abs,abs_of_nonneg hnn]
    exact hb t ht
  have hi := (integrable_natPower_iff_weightedProbabilityTail μ Y hYm hYn q).mpr htail
  refine ⟨hi,?_⟩
  have heq : (∫ a,Y a^(q+1) ∂μ) = ∫ t in Ioi (0:ℝ),weightedProbabilityTail μ Y q t := by
    rw [integral_eq_lintegral_of_nonneg_ae (hYn.mono (fun a ha => pow_nonneg ha _))
      (hYm.pow_const _).aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : 0<t := ht
        dsimp only [weightedProbabilityTail]
        exact mul_nonneg (by positivity) (probabilityTail_nonneg μ Y t)) hw.aestronglyMeasurable]
    congr 1
    exact lintegral_natPower_eq_weightedProbabilityTail μ Y hYm hYn q
  change (∫ a,Y a^(q+1) ∂μ)≤_
  rw [heq]
  calc
    _ ≤ ∫ t in Ioi (0:ℝ),(((q+1 : ℕ) : ℝ)*C)*(t^q*Real.exp (-t)) := by
      apply integral_mono_ae htail hmajor
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hb t ht
    _ = _ := by
      rw [integral_const_mul,(integral_natPower_exp_neg_Ioi q).2,Nat.factorial_succ,Nat.cast_mul]
      ring

end
end JinWishart
#print axioms JinWishart.integral_natPower_exp_neg_Ioi
#print axioms JinWishart.negativeLog_natPower_integrable_integral_le_of_smallball
