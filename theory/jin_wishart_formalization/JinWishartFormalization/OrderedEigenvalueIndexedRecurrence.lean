import JinWishartFormalization.OrderedEigenvalueStrictRecurrence

/-!
# Finite ordered-statistic form of the Theorem 3 recurrence

This applies the atomless strict event recurrence to adjacent entries of a
finite sequence sorted from largest to smallest.  It remains independent of
the Wishart model and of the paper's determinant evaluation of the increment.
-/

open MeasureTheory

namespace JinWishart

/-- In a descending family, saying that `x` lies between two adjacent
statistics is equivalent to saying every statistic below the cut lies below
`x` and every statistic above the cut lies above `x`.  This is the exact
threshold pattern in the event displayed in Theorem 3. -/
theorem orderedFamily_adjacent_event_eq_fullCut
    {Ω : Type*} (s k : ℕ) (hk : k + 1 < s)
    (φ : Fin s → Ω → ℝ)
    (horder : ∀ ω, Antitone (fun i : Fin s => φ i ω)) (x : ℝ) :
    {ω | φ ⟨k + 1, hk⟩ ω < x ∧ x < φ ⟨k, by omega⟩ ω} =
      {ω | (∀ l : Fin s, (⟨k + 1, hk⟩ : Fin s) ≤ l → φ l ω < x) ∧
        (∀ l : Fin s, l ≤ (⟨k, by omega⟩ : Fin s) → x < φ l ω)} := by
  ext ω
  constructor
  · rintro ⟨hlower, hupper⟩
    constructor
    · intro l hle
      exact lt_of_le_of_lt (horder ω hle) hlower
    · intro l hle
      exact lt_of_lt_of_le hupper (horder ω hle)
  · rintro ⟨hlower, hupper⟩
    exact ⟨hlower ⟨k + 1, hk⟩ le_rfl,
      hupper ⟨k, by omega⟩ le_rfl⟩

/-- Adjacent CDFs in a descending finite family differ by the probability
that the threshold lies strictly between the two statistics, provided the
lower statistic has no atom at that threshold. -/
theorem orderedFamily_adjacent_sublevelMass_eq_add_strict
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s k : ℕ) (hk : k + 1 < s)
    (φ : Fin s → Ω → ℝ)
    (hφ : ∀ i, Measurable (φ i))
    (horder : ∀ ω, Antitone (fun i : Fin s => φ i ω))
    (x : ℝ)
    (hAtom : μ {ω | φ ⟨k + 1, hk⟩ ω = x} = 0) :
    μ {ω | φ ⟨k + 1, hk⟩ ω ≤ x} =
      μ {ω | φ ⟨k, by omega⟩ ω ≤ x} +
        μ {ω | φ ⟨k + 1, hk⟩ ω < x ∧ x < φ ⟨k, by omega⟩ ω} := by
  apply orderedPair_sublevelMass_eq_add_strict μ
    (φ ⟨k + 1, hk⟩) (φ ⟨k, by omega⟩)
    (hφ ⟨k + 1, hk⟩) (hφ ⟨k, by omega⟩) x
  · intro ω
    exact horder ω (by simp)
  · exact hAtom

/-- The same recurrence written directly with the full cut event of all
ordered statistics, matching the event part of the paper's Theorem 3. -/
theorem orderedFamily_adjacent_sublevelMass_eq_add_fullCut
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s k : ℕ) (hk : k + 1 < s)
    (φ : Fin s → Ω → ℝ)
    (hφ : ∀ i, Measurable (φ i))
    (horder : ∀ ω, Antitone (fun i : Fin s => φ i ω))
    (x : ℝ)
    (hAtom : μ {ω | φ ⟨k + 1, hk⟩ ω = x} = 0) :
    μ {ω | φ ⟨k + 1, hk⟩ ω ≤ x} =
      μ {ω | φ ⟨k, by omega⟩ ω ≤ x} +
        μ {ω | (∀ l : Fin s, (⟨k + 1, hk⟩ : Fin s) ≤ l → φ l ω < x) ∧
          (∀ l : Fin s, l ≤ (⟨k, by omega⟩ : Fin s) → x < φ l ω)} := by
  rw [orderedFamily_adjacent_sublevelMass_eq_add_strict μ s k hk φ hφ horder x hAtom]
  rw [orderedFamily_adjacent_event_eq_fullCut s k hk φ horder x]

end JinWishart
