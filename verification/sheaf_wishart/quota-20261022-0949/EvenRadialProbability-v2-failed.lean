import JinWishartFormalization.EvenRadialWeightedIntegral
import Mathlib.Probability.Moments.Basic

/-! Codex. Seed2026102402 controls before source.
[需人工审查] Density measure, AE positivity and weighted Bochner conversion.
The measure constructed here is not yet identified with an actual sample law. -/
open MeasureTheory ProbabilityTheory Set
namespace JinWishart
noncomputable section

def evenRadialMeasure (q : ℕ) (a : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity
    (fun r => ENNReal.ofReal (noncentralChiEvenRadialKernel q a r))

private theorem radialKernel_nonneg_ae (q : ℕ) (a : ℝ) :
    0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] noncentralChiEvenRadialKernel q a := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  unfold noncentralChiEvenRadialKernel
  apply mul_nonneg
  · exact mul_nonneg (div_nonneg (pow_nonneg (le_of_lt hr) _) (by positivity)) (Real.exp_pos _).le
  · exact tsum_nonneg (fun n => by positivity)

theorem evenRadialMeasure_isProbabilityMeasure (q : ℕ) (a : ℝ) :
    IsProbabilityMeasure (evenRadialMeasure q a) := by
  constructor
  change ((volume.restrict (Ioi (0 : ℝ))).withDensity
    (fun r => ENNReal.ofReal (noncentralChiEvenRadialKernel q a r))) univ=1
  rw [withDensity_apply _ measurableSet_univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrableOn_noncentralChiEvenRadialKernel q a)
      (radialKernel_nonneg_ae q a), noncentralChiEvenRadialKernel_integral_eq_one]
  norm_num
attribute [instance] evenRadialMeasure_isProbabilityMeasure

theorem evenRadialMeasure_integral (q : ℕ) (a : ℝ) (f : ℝ → ℝ) :
    (∫ r, f r ∂evenRadialMeasure q a) =
      ∫ r in Ioi (0 : ℝ), noncentralChiEvenRadialKernel q a r*f r := by
  unfold evenRadialMeasure
  rw [integral_withDensity_eq_integral_toReal_smul₀
    ((integrableOn_noncentralChiEvenRadialKernel q a).aemeasurable.ennreal_ofReal)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [radialKernel_nonneg_ae q a] with r hr
  rw [ENNReal.toReal_ofReal hr, smul_eq_mul]

theorem evenRadialMeasure_mgf (q : ℕ) (a t : ℝ) (ht : t<1) :
    mgf (fun r : ℝ => r^2/2) (evenRadialMeasure q a) t =
      Real.exp (a^2*t/(2*(1-t)))/(1-t)^(q+1) := by
  unfold mgf
  rw [evenRadialMeasure_integral]
  simpa only [mul_div_assoc, mul_comm] using evenRadialKernel_mgf_integral q a t ht

theorem evenRadialMeasure_integrable_exp_energy (q : ℕ) (a t : ℝ) (ht : t<1) :
    Integrable (fun r : ℝ => Real.exp (t*(r^2/2))) (evenRadialMeasure q a) := by
  apply Integrable.of_integral_ne_zero
  change mgf (fun r : ℝ => r^2/2) (evenRadialMeasure q a) t ≠ 0
  rw [evenRadialMeasure_mgf q a t ht]
  exact ne_of_gt (div_pos (Real.exp_pos _) (pow_pos (sub_pos.mpr ht) _))

end
end JinWishart
#print axioms JinWishart.evenRadialMeasure_isProbabilityMeasure
#print axioms JinWishart.evenRadialMeasure_integral
#print axioms JinWishart.evenRadialMeasure_mgf
#print axioms JinWishart.evenRadialMeasure_integrable_exp_energy
