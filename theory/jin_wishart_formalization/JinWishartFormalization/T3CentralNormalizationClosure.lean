import JinWishartFormalization.T3CentralNormalizationWitness
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Retrieval-assisted closure of the concrete T3 normalization test

LeanSearch suggested `Finset.powersetCard_one`. We verified it against the
locked mathlib and use it to close the previous generic-sum API gap.
This disproves probability identification of this SOURCE-TRANSCRIBED
candidate at s=2,t=3,L=0,k=2,x=2, not the final journal theorem or a
corrected normalization. [需人工审查] Source and model interpretation.
-/

open Finset MeasureTheory
namespace JinWishart
noncomputable section

/-- Selecting exactly one row is a sum over singleton row selections.
This is a local consequence of existing mathlib results, not a novel theorem. -/
theorem sum_powerset_card_one {α β : Type*} [DecidableEq α] [AddCommMonoid β]
    (s : Finset α) (f : Finset α → β) :
    (∑ S ∈ s.powerset, if S.card = 1 then f S else 0) = ∑ i ∈ s, f {i} := by
  rw [← Finset.sum_filter, ← Finset.powersetCard_eq_filter,
    Finset.powersetCard_one, Finset.sum_map]
  rfl

/-- The generic fixed-cardinality API now matches the two explicit row terms. -/
theorem theorem3CentralTwoThreeCandidate_eq_mixedRowSum :
    theorem3IncrementCandidate 2 3 0 2 (by decide) (by decide)
      emptyNoncentralSpectrum 2 = centralTwoThreeMixedRowSum := by
  have hc : theorem3C3 2 3 0 (by decide) emptyNoncentralSpectrum = 1 := by
    norm_num [theorem3C3, theorem3GammaFactor, Fin.prod_univ_succ]
  simp only [theorem3IncrementCandidate, hc, Complex.ofReal_one, one_mul,
    theorem3ThetaDetSum, show 2 - 1 = 1 by decide]
  rw [sum_powerset_card_one, Fin.sum_univ_two]
  rfl

theorem theorem3CentralTwoThreeCandidate_gt_one :
    1 < (theorem3IncrementCandidate 2 3 0 2 (by decide) (by decide)
      emptyNoncentralSpectrum 2).re := by
  rw [theorem3CentralTwoThreeCandidate_eq_mixedRowSum]
  exact theorem3CentralTwoThree_at_two_gt_one

/-- This exact transcription cannot equal any event probability.
No proposed spectral-density identity is assumed. -/
theorem theorem3CentralTwoThreeCandidate_ne_eventProbability
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (B : Set Ω) :
    (theorem3IncrementCandidate 2 3 0 2 (by decide) (by decide)
      emptyNoncentralSpectrum 2).re ≠ μ.real B := by
  exact ne_of_gt (lt_of_le_of_lt (measureReal_le_one (μ := μ) (s := B))
    theorem3CentralTwoThreeCandidate_gt_one)

end
end JinWishart
