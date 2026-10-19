import JinWishartFormalization.ProbabilityTailFirstMoment
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Positive integer moments as weighted probability-tail integrals

The index q below describes moment q+1, with weight (q+1)t^q.
Codex. [需人工审查] Weighted layercake/Fubini and critical moment interpretation.
-/
open Filter Set MeasureTheory
namespace JinWishart
noncomputable section
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]

def weightedProbabilityTail (f : α → ℝ) (q : ℕ) (t : ℝ) : ℝ :=
  ((q+1 : ℕ) : ℝ)*t^q*probabilityTail μ f t

theorem measurable_weightedProbabilityTail (f : α → ℝ) (q : ℕ) :
    Measurable (weightedProbabilityTail μ f q) := by
  unfold weightedProbabilityTail
  exact (measurable_const.mul (measurable_id.pow_const q)).mul (measurable_probabilityTail μ f)

theorem lintegral_natPower_eq_weightedProbabilityTail (f : α → ℝ)
    (hf : Measurable f) (hnn : 0 ≤ᵐ[μ] f) (q : ℕ) :
    (∫⁻ a, ENNReal.ofReal (f a^(q+1)) ∂μ) =
      ∫⁻ t in Ioi 0, ENNReal.ofReal (weightedProbabilityTail μ f q t) := by
  have hG (u : ℝ) : (∫ t in (0 : ℝ)..u, ((q+1 : ℕ) : ℝ)*t^q) = u^(q+1) := by
    rw [intervalIntegral.integral_const_mul,integral_pow]
    simp only [zero_pow (Nat.succ_ne_zero q),sub_zero]
    push_cast
    field_simp
  have h := lintegral_comp_eq_lintegral_meas_le_mul μ
    (g := fun t : ℝ => ((q+1 : ℕ) : ℝ)*t^q) hnn hf.aemeasurable
    (fun t _ => (continuous_const.mul (continuous_id.pow q)).intervalIntegrable 0 t)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (0 : ℝ)<t := ht
      positivity)
  simp_rw [hG] at h
  rw [h]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : (0 : ℝ)<t := ht
  rw [show μ {a | t≤f a} = ENNReal.ofReal (probabilityTail μ f t) from
    (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm,
    ← ENNReal.ofReal_mul (probabilityTail_nonneg μ f t)]
  congr 1
  unfold weightedProbabilityTail
  ring

theorem integrable_natPower_iff_weightedProbabilityTail (f : α → ℝ)
    (hf : Measurable f) (hnn : 0 ≤ᵐ[μ] f) (q : ℕ) :
    Integrable (fun a => f a^(q+1)) μ ↔ IntegrableOn (weightedProbabilityTail μ f q) (Ioi 0) := by
  have hp : 0 ≤ᵐ[μ] (fun a => f a^(q+1)) := hnn.mono (fun _ h => pow_nonneg h _)
  have hw : 0 ≤ᵐ[volume.restrict (Ioi 0)] weightedProbabilityTail μ f q := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ)<t := ht
    exact mul_nonneg (by positivity) (probabilityTail_nonneg μ f t)
  change Integrable (fun a => f a^(q+1)) μ ↔
    Integrable (weightedProbabilityTail μ f q) (volume.restrict (Ioi 0))
  rw [← lintegral_ofReal_ne_top_iff_integrable (hf.pow_const (q+1)).aestronglyMeasurable hp,
    ← lintegral_ofReal_ne_top_iff_integrable
      (measurable_weightedProbabilityTail μ f q).aestronglyMeasurable hw,
    lintegral_natPower_eq_weightedProbabilityTail μ f hf hnn q]

theorem weightedProbabilityTail_integrableOn_near_zero (f : α → ℝ) (q : ℕ) :
    IntegrableOn (weightedProbabilityTail μ f q) (Ioc (0 : ℝ) 4) := by
  apply (integrable_const (((q+1 : ℕ) : ℝ)*(4 : ℝ)^q)).mono'
    (measurable_weightedProbabilityTail μ f q).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht0 : 0≤t := ht.1.le
  have hw0 : 0 ≤ ((q+1 : ℕ) : ℝ)*t^q := by positivity
  dsimp only [weightedProbabilityTail]
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hw0 (probabilityTail_nonneg μ f t))]
  exact (mul_le_of_le_one_right hw0 (probabilityTail_le_one μ f t)).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht0 ht.2 q) (by positivity))

theorem integrable_succPower_iff_two_sided_power_tail (f : α → ℝ)
    (hf : Measurable f) (hnn : 0 ≤ᵐ[μ] f) (q k : ℕ)
    (c C : ℝ) (hc : 0<c) (hC : 0<C)
    (hb : ∀ t : ℝ, 4≤t → c/t^k ≤ probabilityTail μ f t ∧ probabilityTail μ f t ≤ C/t^k) :
    Integrable (fun a => f a^(q+1)) μ ↔ q+1<k := by
  rw [integrable_natPower_iff_weightedProbabilityTail μ f hf hnn q,
    ← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ)≤4),integrableOn_union]
  simp only [weightedProbabilityTail_integrableOn_near_zero,true_and]
  apply integrableOn_powerTail_iff (weightedProbabilityTail μ f q)
    (measurable_weightedProbabilityTail μ f q) (by
      intro t ht
      have ht4 : (4 : ℝ)<t := ht
      have ht0 : 0<t := by linarith
      exact mul_nonneg (by positivity) (probabilityTail_nonneg μ f t)) q k
    (c*((q+1 : ℕ) : ℝ)) (C*((q+1 : ℕ) : ℝ)) (by positivity) (by positivity)
  intro t ht
  have ht4 : (4 : ℝ)<t := ht
  have ht0 : 0<t := by linarith
  have hw : 0≤((q+1 : ℕ) : ℝ)*t^q := by positivity
  have hlo := mul_le_mul_of_nonneg_left (hb t ht4.le).1 hw
  have hup := mul_le_mul_of_nonneg_left (hb t ht4.le).2 hw
  constructor
  · convert hlo using 1 <;> (try dsimp only [weightedProbabilityTail]) <;> ring
  · convert hup using 1 <;> (try dsimp only [weightedProbabilityTail]) <;> ring

theorem integrable_natPower_iff_two_sided_power_tail (f : α → ℝ)
    (hf : Measurable f) (hnn : 0 ≤ᵐ[μ] f) (q k : ℕ) (hk : 0<k)
    (c C : ℝ) (hc : 0<c) (hC : 0<C)
    (hb : ∀ t : ℝ, 4≤t → c/t^k ≤ probabilityTail μ f t ∧ probabilityTail μ f t ≤ C/t^k) :
    Integrable (fun a => f a^q) μ ↔ q<k := by
  cases q with
  | zero => simp only [pow_zero,hk,iff_true]; exact integrable_const 1
  | succ q => exact integrable_succPower_iff_two_sided_power_tail μ f hf hnn q k c C hc hC hb

end
end JinWishart
#print axioms JinWishart.measurable_weightedProbabilityTail
#print axioms JinWishart.lintegral_natPower_eq_weightedProbabilityTail
#print axioms JinWishart.integrable_natPower_iff_weightedProbabilityTail
#print axioms JinWishart.weightedProbabilityTail_integrableOn_near_zero
#print axioms JinWishart.integrable_succPower_iff_two_sided_power_tail
#print axioms JinWishart.integrable_natPower_iff_two_sided_power_tail
