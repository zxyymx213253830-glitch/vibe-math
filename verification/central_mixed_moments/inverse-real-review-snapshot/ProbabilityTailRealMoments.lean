import JinWishartFormalization.ProbabilityTailFirstMoment
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Positive real moments from two-sided probability-tail bounds

Unlike natural weights, p*t^(p-1) is unbounded near0 when0<p<1.
It is dominated by an integrable real power there, not by a constant.
Codex. [需人工审查] Real powers, weighted layercake/Fubini and critical threshold.
-/
open Filter Set MeasureTheory
namespace JinWishart
noncomputable section
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]

def realWeightedProbabilityTail (f : α → ℝ) (p t : ℝ) : ℝ :=
  p*t^(p-1)*probabilityTail μ f t

theorem measurable_realWeightedProbabilityTail (f : α → ℝ) (p : ℝ) :
    Measurable (realWeightedProbabilityTail μ f p) := by
  unfold realWeightedProbabilityTail
  exact (measurable_const.mul (measurable_id.pow_const (p-1))).mul (measurable_probabilityTail μ f)

theorem lintegral_rpow_eq_realWeightedProbabilityTail (f : α → ℝ)
    (hf : Measurable f) (hnn : 0 ≤ᵐ[μ] f) (p : ℝ) (hp : 0<p) :
    (∫⁻ a, ENNReal.ofReal (f a^p) ∂μ) =
      ∫⁻ t in Ioi 0, ENNReal.ofReal (realWeightedProbabilityTail μ f p t) := by
  have hG (u : ℝ) : (∫ t in (0 : ℝ)..u, p*t^(p-1)) = u^p := by
    rw [intervalIntegral.integral_const_mul,integral_rpow (Or.inl (by linarith : -1<p-1))]
    simp only [sub_add_cancel,Real.zero_rpow hp.ne',sub_zero]
    field_simp
  have h := lintegral_comp_eq_lintegral_meas_le_mul μ
    (g := fun t : ℝ => p*t^(p-1)) hnn hf.aemeasurable
    (fun t _ => (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1<p-1)).const_mul p)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg hp.le (Real.rpow_nonneg (le_of_lt ht) _))
  simp_rw [hG] at h
  rw [h]
  apply lintegral_congr_ae
  filter_upwards [] with t
  rw [show μ {a | t≤f a} = ENNReal.ofReal (probabilityTail μ f t) from
    (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm,
    ← ENNReal.ofReal_mul (probabilityTail_nonneg μ f t)]
  congr 1
  unfold realWeightedProbabilityTail
  ring

theorem integrable_rpow_iff_realWeightedProbabilityTail (f : α → ℝ)
    (hf : Measurable f) (hnn : 0 ≤ᵐ[μ] f) (p : ℝ) (hp : 0<p) :
    Integrable (fun a => f a^p) μ ↔ IntegrableOn (realWeightedProbabilityTail μ f p) (Ioi 0) := by
  have hpnn : 0 ≤ᵐ[μ] (fun a => f a^p) := hnn.mono (fun _ h => Real.rpow_nonneg h _)
  have hw : 0 ≤ᵐ[volume.restrict (Ioi 0)] realWeightedProbabilityTail μ f p := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (mul_nonneg hp.le (Real.rpow_nonneg (le_of_lt ht) _))
      (probabilityTail_nonneg μ f t)
  change Integrable (fun a => f a^p) μ ↔
    Integrable (realWeightedProbabilityTail μ f p) (volume.restrict (Ioi 0))
  rw [← lintegral_ofReal_ne_top_iff_integrable (hf.pow_const p).aestronglyMeasurable hpnn,
    ← lintegral_ofReal_ne_top_iff_integrable
      (measurable_realWeightedProbabilityTail μ f p).aestronglyMeasurable hw,
    lintegral_rpow_eq_realWeightedProbabilityTail μ f hf hnn p hp]

theorem realWeightedProbabilityTail_integrableOn_near_zero (f : α → ℝ) (p : ℝ) (hp : 0<p) :
    IntegrableOn (realWeightedProbabilityTail μ f p) (Ioc (0 : ℝ) 4) := by
  have hg : IntervalIntegrable (fun t : ℝ => t^(p-1)) volume 0 4 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  apply (hg.1.const_mul p).mono'
    (measurable_realWeightedProbabilityTail μ f p).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have hw0 : 0≤p*t^(p-1) := mul_nonneg hp.le (Real.rpow_nonneg ht.1.le _)
  dsimp only [realWeightedProbabilityTail]
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hw0 (probabilityTail_nonneg μ f t))]
  exact mul_le_of_le_one_right hw0 (probabilityTail_le_one μ f t)

theorem integrable_positiveRealPower_iff_two_sided_power_tail (f : α → ℝ)
    (hf : Measurable f) (hnn : 0 ≤ᵐ[μ] f) (p : ℝ) (hp : 0<p) (k : ℕ)
    (c C : ℝ) (hc : 0<c) (hC : 0<C)
    (hb : ∀ t : ℝ, 4≤t → c/t^k ≤ probabilityTail μ f t ∧ probabilityTail μ f t ≤ C/t^k) :
    Integrable (fun a => f a^p) μ ↔ p<(k : ℝ) := by
  rw [integrable_rpow_iff_realWeightedProbabilityTail μ f hf hnn p hp,
    ← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ)≤4),integrableOn_union]
  simp only [realWeightedProbabilityTail_integrableOn_near_zero μ f p hp,true_and]
  have hcompare := integrableOn_positive_sandwich_iff (realWeightedProbabilityTail μ f p)
    (fun t : ℝ => t^((p-1)-(k : ℝ))) (Ioi 4)
    (measurable_realWeightedProbabilityTail μ f p) (by fun_prop)
    (by intro t ht; have ht4 : (4 : ℝ)<t := ht; exact
      mul_nonneg (mul_nonneg hp.le (Real.rpow_nonneg (by linarith) _)) (probabilityTail_nonneg μ f t))
    (by intro t ht; have ht4 : (4 : ℝ)<t := ht; exact Real.rpow_nonneg (by linarith) _)
    (p*c) (p*C) (mul_pos hp hc) (mul_pos hp hC) (by
      intro t ht
      have ht4 : (4 : ℝ)<t := ht
      have ht0 : 0<t := by linarith
      have hw : 0≤p*t^(p-1) := mul_nonneg hp.le (Real.rpow_nonneg ht0.le _)
      have hlo := mul_le_mul_of_nonneg_left (hb t ht4.le).1 hw
      have hup := mul_le_mul_of_nonneg_left (hb t ht4.le).2 hw
      rw [Real.rpow_sub ht0,Real.rpow_natCast]
      constructor
      · convert hlo using 1 <;> (try dsimp only [realWeightedProbabilityTail]) <;> ring
      · convert hup using 1 <;> (try dsimp only [realWeightedProbabilityTail]) <;> ring)
    measurableSet_Ioi
  rw [hcompare,integrableOn_Ioi_rpow_iff (by norm_num : (0 : ℝ)<4)]
  constructor <;> intro h <;> linarith

end
end JinWishart
#print axioms JinWishart.measurable_realWeightedProbabilityTail
#print axioms JinWishart.lintegral_rpow_eq_realWeightedProbabilityTail
#print axioms JinWishart.integrable_rpow_iff_realWeightedProbabilityTail
#print axioms JinWishart.realWeightedProbabilityTail_integrableOn_near_zero
#print axioms JinWishart.integrable_positiveRealPower_iff_two_sided_power_tail
