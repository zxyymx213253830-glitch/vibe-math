import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# MIMO scalar-SNR performance identities

This file isolates the threshold-scaling step in the paper's outage analysis. It is
independent of the still-missing measurable ordered-eigenvalue random variables, so the
results below do not by themselves establish the Wishart outage formula.
-/

open MeasureTheory

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

end JinWishart
