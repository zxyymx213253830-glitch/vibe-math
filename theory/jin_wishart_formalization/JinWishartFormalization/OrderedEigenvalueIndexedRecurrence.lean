import JinWishartFormalization.OrderedEigenvalueStrictRecurrence

/-!
# Finite ordered-statistic form of the Theorem 3 recurrence

This applies the atomless strict event recurrence to adjacent entries of a
finite sequence sorted from largest to smallest.  It remains independent of
the Wishart model and of the paper's determinant evaluation of the increment.
-/

open MeasureTheory

namespace JinWishart

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

end JinWishart
