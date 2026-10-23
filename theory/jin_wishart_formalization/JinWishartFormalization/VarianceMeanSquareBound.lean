import JinWishartFormalization.MeanSquareSecondMomentContinuity
import Mathlib.Probability.Moments.Variance

/-! Variance difference from a mean-square error, with no independence.
Codex. Controls seed2026102240:72 discrete models/365 checks, tight two-point
reference. [需人工审查] Centering, probability measure and L2 interpretation. -/
open MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

theorem variance_difference_le_mean_square {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (u v : α → ℝ)
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    |variance u μ-variance v μ|≤(∫ a,(u a-v a)^2 ∂μ)+
      2*Real.sqrt (∫ a,(u a-v a)^2 ∂μ)*Real.sqrt (variance v μ) := by
  let uc := fun a => u a-∫ z,u z ∂μ
  let vc := fun a => v a-∫ z,v z ∂μ
  let e := fun a => u a-v a
  have huc : MemLp uc 2 μ := hu.sub (memLp_const _)
  have hvc : MemLp vc 2 μ := hv.sub (memLp_const _)
  have he : MemLp e 2 μ := hu.sub hv
  have hU : (∫ a,(uc a)^2 ∂μ)=variance u μ := (variance_eq_integral hu.aemeasurable).symm
  have hV : (∫ a,(vc a)^2 ∂μ)=variance v μ := (variance_eq_integral hv.aemeasurable).symm
  have hJ : (∫ a,(uc a-vc a)^2 ∂μ)=variance e μ := by
    rw [variance_eq_integral he.aemeasurable]
    apply integral_congr_ae
    exact ae_of_all _ (fun a => by
      dsimp only [uc,vc,e]
      rw [integral_sub (hu.integrable one_le_two) (hv.integrable one_le_two)]
      ring)
  have hh := integral_square_difference_bound μ uc vc huc hvc
  rw [hU,hV,hJ] at hh
  have hvar := variance_eq_sub he
  change variance e μ=(∫ a,(e a)^2 ∂μ)-(∫ a,e a ∂μ)^2 at hvar
  have hle : variance e μ≤∫ a,(e a)^2 ∂μ := by rw [hvar];nlinarith [sq_nonneg (∫ a,e a ∂μ)]
  have hsq := Real.sqrt_le_sqrt hle
  have hnon := Real.sqrt_nonneg (variance v μ)
  change |variance u μ-variance v μ|≤(∫ a,(e a)^2 ∂μ)+
    2*Real.sqrt (∫ a,(e a)^2 ∂μ)*Real.sqrt (variance v μ)
  nlinarith

end
end JinWishart
#print axioms JinWishart.variance_difference_le_mean_square
