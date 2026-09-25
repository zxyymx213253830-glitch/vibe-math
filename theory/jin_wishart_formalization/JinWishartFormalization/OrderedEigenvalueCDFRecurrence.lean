import JinWishartFormalization.WishartProbability

/-!
# Event recurrence underlying Theorem 3

For two ordered real random variables `a ≤ b`, the CDF of `a` splits
into the CDF of `b` and the probability that the threshold lies between
them.  This is the event-level part of the paper's Theorem 3 recurrence.
The determinant evaluation of the increment is a separate result.
-/

open MeasureTheory Set

namespace JinWishart

/-- Exact set decomposition for a pair of ordered real statistics. -/
theorem orderedPair_sublevel_eq_union {Ω : Type*}
    (a b : Ω → ℝ) (x : ℝ) (horder : ∀ ω, a ω ≤ b ω) :
    {ω | a ω ≤ x} =
      {ω | b ω ≤ x} ∪ {ω | a ω ≤ x ∧ x < b ω} := by
  ext ω
  constructor
  · intro ha
    by_cases hb : b ω ≤ x
    · exact Or.inl hb
    · exact Or.inr ⟨ha, lt_of_not_ge hb⟩
  · rintro (hb | ⟨ha, _⟩)
    · exact le_trans (horder ω) hb
    · exact ha

/-- For ordered measurable statistics, their sublevel masses obey the
exact recurrence without any atom or strict-ordering assumptions. -/
theorem orderedPair_sublevelMass_eq_add {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (a b : Ω → ℝ)
    (ha : Measurable a) (hb : Measurable b)
    (x : ℝ) (horder : ∀ ω, a ω ≤ b ω) :
    μ {ω | a ω ≤ x} =
      μ {ω | b ω ≤ x} + μ {ω | a ω ≤ x ∧ x < b ω} := by
  let A : Set Ω := {ω | b ω ≤ x}
  let B : Set Ω := {ω | a ω ≤ x ∧ x < b ω}
  have hB : MeasurableSet B :=
    (measurableSet_le ha measurable_const).inter
      (measurableSet_lt measurable_const hb)
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    intro ω hA hB
    exact (not_lt_of_ge hA) hB.2
  rw [orderedPair_sublevel_eq_union a b x horder]
  exact measure_union hdisj hB

end JinWishart
