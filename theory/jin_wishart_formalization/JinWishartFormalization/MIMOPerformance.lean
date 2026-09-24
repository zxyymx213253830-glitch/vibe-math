import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# MIMO scalar-SNR performance identities

This file isolates the threshold-scaling step in the paper's outage analysis. It is
independent of the still-missing measurable ordered-eigenvalue random variables, so the
results below do not by themselves establish the Wishart outage formula.
-/

open MeasureTheory
open Set

namespace JinWishart

/-- The weak CDF convention `P(φ ≤ x)` for a real-valued statistic. -/
noncomputable def statisticCDF {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (φ : Ω → ℝ) (x : ℝ) : ENNReal :=
  μ {ω | φ ω ≤ x}

/-- Weak outage probability for an SNR obtained by scaling a nonnegative channel statistic. -/
noncomputable def weakOutageProbability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (φ : Ω → ℝ) (scale threshold : ℝ) : ENNReal :=
  μ {ω | scale * φ ω ≤ threshold}

/-- Strict outage probability, kept separate because it equals the weak CDF only
when the threshold event has zero mass. -/
noncomputable def strictOutageProbability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (φ : Ω → ℝ) (scale threshold : ℝ) : ENNReal :=
  μ {ω | scale * φ ω < threshold}

/-- Under a probability measure, the strict upper tail is the complement of the
weak CDF. This identity itself does not require an atomlessness assumption. -/
theorem strictTail_eq_one_sub_statisticCDF {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (φ : Ω → ℝ) (x : ℝ)
    (hφ : Measurable φ) :
    μ {ω | x < φ ω} = 1 - statisticCDF μ φ x := by
  have hset : {ω | x < φ ω} = ({ω | φ ω ≤ x})ᶜ := by
    ext ω
    simp
  rw [hset]
  change μ ((fun ω => φ ω) ⁻¹' Set.Iic x)ᶜ =
    1 - μ ((fun ω => φ ω) ⁻¹' Set.Iic x)
  rw [measure_compl (hφ measurableSet_Iic) (measure_ne_top μ _)]
  simp

/-- For positive scale, the weak outage threshold is exactly the statistic CDF
at the rescaled threshold. -/
theorem weakOutageProbability_eq_statisticCDF {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (φ : Ω → ℝ) (scale threshold : ℝ) (hscale : 0 < scale) :
    weakOutageProbability μ φ scale threshold =
      statisticCDF μ φ (threshold / scale) := by
  unfold weakOutageProbability statisticCDF
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq]
  rw [le_div_iff₀ hscale]
  simp [mul_comm]

/-- The corresponding identity for the strict convention. Converting this to the
weak CDF convention requires a separate no-atom argument at the threshold. -/
theorem strictOutageProbability_eq_strictStatisticCDF {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (φ : Ω → ℝ) (scale threshold : ℝ) (hscale : 0 < scale) :
    strictOutageProbability μ φ scale threshold =
      μ {ω | φ ω < threshold / scale} := by
  unfold strictOutageProbability
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq]
  rw [lt_div_iff₀ hscale]
  simp [mul_comm]

/-- Strict and weak CDFs agree at a level when that level set has zero mass.
This isolates the no-atom obligation needed to replace strict tails by the
paper's weak-CDF convention. -/
theorem measure_strictLevel_eq_weakLevel_of_null {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (φ : Ω → ℝ) (x : ℝ) (hφ : Measurable φ)
    (hnull : μ {ω | φ ω = x} = 0) :
    μ {ω | φ ω < x} = μ {ω | φ ω ≤ x} := by
  have hstrict : MeasurableSet {ω | φ ω < x} := hφ measurableSet_Iio
  have hlevel : MeasurableSet {ω | φ ω = x} := hφ (measurableSet_singleton x)
  have hdisj : Disjoint {ω | φ ω < x} {ω | φ ω = x} := by
    rw [Set.disjoint_left]
    rintro ω hlt heq
    change φ ω < x at hlt
    change φ ω = x at heq
    rw [heq] at hlt
    exact (lt_irrefl x hlt)
  have hunion : {ω | φ ω ≤ x} = {ω | φ ω < x} ∪ {ω | φ ω = x} := by
    ext ω
    simp [le_iff_lt_or_eq]
  rw [hunion, measure_union hdisj hlevel, hnull]
  simp

/-- At a non-atomic threshold, strict outage and weak outage have equal mass. -/
theorem strictOutageProbability_eq_weakOutageProbability_of_levelSet_null
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (φ : Ω → ℝ)
    (scale threshold : ℝ) (hscale : 0 < scale) (hφ : Measurable φ)
    (hnull : μ {ω | φ ω = threshold / scale} = 0) :
    strictOutageProbability μ φ scale threshold =
      weakOutageProbability μ φ scale threshold := by
  rw [strictOutageProbability_eq_strictStatisticCDF μ φ scale threshold hscale,
    weakOutageProbability_eq_statisticCDF μ φ scale threshold hscale]
  exact measure_strictLevel_eq_weakLevel_of_null μ φ (threshold / scale) hφ hnull

/-- Layer-cake form of an averaged increasing error kernel: if `G(z)=∫₀ᶻ g(t)dt`,
then its expectation is a tail-probability integral. This is the measure-theoretic step
used when converting an average SER kernel into a CDF integral; the Gaussian-Q identity
and its concrete derivative kernel must still be supplied separately. -/
theorem meanIntegratedKernel_eq_tailIntegral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) (g : ℝ → ℝ)
    (hf_nonneg : 0 ≤ᵐ[μ] f) (hf_aemeasurable : AEMeasurable f μ)
    (hg_intervalIntegrable : ∀ t > 0, IntervalIntegrable g volume 0 t)
    (hg_nonneg : ∀ᵐ t ∂volume.restrict (Ioi 0), 0 ≤ g t) :
    ∫⁻ ω, ENNReal.ofReal (∫ t in (0 : ℝ)..f ω, g t) ∂μ =
      ∫⁻ t in Ioi 0, μ {ω | t < f ω} * ENNReal.ofReal (g t) :=
  lintegral_comp_eq_lintegral_meas_lt_mul μ hf_nonneg hf_aemeasurable
    hg_intervalIntegrable hg_nonneg

end JinWishart
