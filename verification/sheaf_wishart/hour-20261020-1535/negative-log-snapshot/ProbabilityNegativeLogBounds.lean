import JinWishartFormalization.ProbabilityTailIntegrability

/-! A uniform one-sided logarithmic moment from a linear small-ball bound.
Codex. [需人工审查] Layercake/Tonelli, measurability and totalized Real.log 0.
No positivity assumption is needed for the upper-tail inclusion below.
-/
open MeasureTheory Set Filter
namespace JinWishart
noncomputable section
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]

theorem negativeLog_probabilityTail_le (f : α → ℝ) (C : ℝ)
    (hsmall : ∀ x : ℝ, 0 < x → μ.real {a | f a ≤ x} ≤ C*x)
    (t : ℝ) (ht : 0 < t) :
    probabilityTail μ (fun a => max 0 (-Real.log (f a))) t ≤ C*Real.exp (-t) := by
  apply le_trans (show probabilityTail μ (fun a => max 0 (-Real.log (f a))) t ≤
      μ.real {a | f a ≤ Real.exp (-t)} from ?_) (hsmall _ (Real.exp_pos _))
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro a ha
  change t ≤ max 0 (-Real.log (f a)) at ha
  change f a ≤ Real.exp (-t)
  have hlog : Real.log (f a) ≤ -t := by
    rcases le_max_iff.mp ha with h | h
    · linarith
    · linarith
  by_cases hf : 0 < f a
  · simpa only [Real.exp_log hf] using Real.exp_le_exp.mpr hlog
  · exact (le_of_not_gt hf).trans (Real.exp_pos _).le

theorem negativeLog_integrable_integral_le_of_smallball
    (f : α → ℝ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C)
    (hsmall : ∀ x : ℝ, 0 < x → μ.real {a | f a ≤ x} ≤ C*x) :
    Integrable (fun a => max 0 (-Real.log (f a))) μ ∧
      (∫ a, max 0 (-Real.log (f a)) ∂μ) ≤ C := by
  let Y : α → ℝ := fun a => max 0 (-Real.log (f a))
  have hYm : Measurable Y := measurable_const.max (hf.log.neg)
  have hYn : 0 ≤ᵐ[μ] Y := ae_of_all _ (fun a => le_max_left _ _)
  have hmajor : IntegrableOn (fun t : ℝ => C*Real.exp (-t)) (Ioi 0) :=
    (integrableOn_exp_neg_Ioi 0).const_mul C
  have htbound : ∀ t : ℝ, 0 < t → probabilityTail μ Y t ≤ C*Real.exp (-t) :=
    negativeLog_probabilityTail_le μ f C hsmall
  have htail : IntegrableOn (probabilityTail μ Y) (Ioi 0) := by
    apply hmajor.mono' (measurable_probabilityTail μ Y).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (probabilityTail_nonneg μ Y t)]
    exact htbound t ht
  have hi : Integrable Y μ :=
    (integrable_nonneg_iff_probabilityTail μ Y hYm hYn).mpr htail
  refine ⟨hi, ?_⟩
  have heq : (∫ a, Y a ∂μ) = ∫ t in Ioi (0 : ℝ), probabilityTail μ Y t := by
    rw [integral_eq_lintegral_of_nonneg_ae hYn hYm.aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae
        (ae_of_all _ (probabilityTail_nonneg μ Y))
        (measurable_probabilityTail μ Y).aestronglyMeasurable]
    congr 1
    rw [lintegral_eq_lintegral_meas_le μ hYn hYm.aemeasurable]
    apply lintegral_congr_ae
    filter_upwards [] with t
    exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  change (∫ a, Y a ∂μ) ≤ C
  rw [heq]
  calc
    _ ≤ ∫ t in Ioi (0 : ℝ), C*Real.exp (-t) := by
      apply integral_mono_ae htail hmajor
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact htbound t ht
    _ = C := by rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]

end
end JinWishart
#print axioms JinWishart.negativeLog_probabilityTail_le
#print axioms JinWishart.negativeLog_integrable_integral_le_of_smallball
