import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# A probability measure from a smooth primitive on the positive half-line

Generic measure reconstruction, not a target-density assumption. Applications
must supply an independently established actual CDF. Codex.
[需人工审查] Measure extensionality, FTC and boundary/atom interpretation.
-/
open Filter Set MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

theorem measure_eq_withDensity_of_positive_primitive (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (G h : ℝ → ℝ) (h0 : G 0=0)
    (hCDF : ∀ x : ℝ, cdf μ x=if 0≤x then G x else 0)
    (hh : Continuous h) (hd : ∀ x : ℝ, HasDerivAt G (h x) x)
    (hnn : ∀ x : ℝ, 0<x → 0≤h x) :
    μ=volume.withDensity ((Ioi (0 : ℝ)).indicator (fun x => ENNReal.ofReal (h x))) := by
  apply Measure.ext_of_Iic
  intro x
  rw [← ofReal_cdf μ x,hCDF x,withDensity_apply _ measurableSet_Iic,
    lintegral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi]
  have hset : Ioi (0 : ℝ) ∩ Iic x=Ioc 0 x := by ext y; simp
  rw [hset]
  by_cases hx : 0≤x
  · rw [ite_eq_left hx]
    have hi : IntervalIntegrable h volume 0 x := hh.intervalIntegrable 0 x
    have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc 0 x)] h := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
      exact hnn y hy.1
    rw [← ofReal_integral_eq_lintegral_ofReal hi.1 hnonneg,
      ← intervalIntegral.integral_of_le hx,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y) hi,h0,sub_zero]
  · rw [ite_eq_right hx,Ioc_eq_empty (not_lt.mpr (le_of_not_ge hx)),Measure.restrict_empty,lintegral_zero_measure,
      ENNReal.ofReal_zero]

theorem primitive_derivative_nonneg_of_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (G h : ℝ → ℝ) (hCDF : ∀ x : ℝ, cdf μ x=if 0≤x then G x else 0)
    (hd : ∀ x : ℝ, HasDerivAt G (h x) x) (x : ℝ) (hx : 0<x) : 0≤h x := by
  have he : (fun t => cdf μ t) =ᶠ[nhds x] G := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    rw [hCDF y,ite_eq_left hy.le]
  have hg := (monotone_cdf μ).deriv_nonneg (x := x)
  rw [he.deriv_eq,(hd x).deriv] at hg
  exact hg

end
end JinWishart
#print axioms JinWishart.measure_eq_withDensity_of_positive_primitive
#print axioms JinWishart.primitive_derivative_nonneg_of_cdf
