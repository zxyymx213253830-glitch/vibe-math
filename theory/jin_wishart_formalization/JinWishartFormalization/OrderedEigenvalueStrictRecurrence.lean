import JinWishartFormalization.OrderedEigenvalueCDFRecurrence

/-!
# Removing the boundary in the ordered-CDF recurrence

The paper writes the increment event with strict inequalities.  The exact
set decomposition naturally uses a weak lower threshold.  This module proves
that the two events have equal measure when the lower statistic has no atom
at the threshold.  This is an abstract probability lemma; the paper's
multi-eigenvalue no-atom and no-collision facts are separate obligations.
-/

open MeasureTheory Set

namespace JinWishart

/-- A zero-mass boundary allows the lower threshold in the increment event
to be made strict. -/
theorem orderedPair_increment_weak_eq_strict {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (a b : Ω → ℝ) (ha : Measurable a) (hb : Measurable b)
    (x : ℝ) (hAtom : μ {ω | a ω = x} = 0) :
    μ {ω | a ω ≤ x ∧ x < b ω} =
      μ {ω | a ω < x ∧ x < b ω} := by
  let A : Set Ω := {ω | a ω < x ∧ x < b ω}
  let B : Set Ω := {ω | a ω = x ∧ x < b ω}
  have hset : {ω | a ω ≤ x ∧ x < b ω} = A ∪ B := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union, A, B]
    constructor
    · rintro ⟨hle, hbω⟩
      rcases hle.lt_or_eq with hlt | heq
      · exact Or.inl ⟨hlt, hbω⟩
      · exact Or.inr ⟨heq, hbω⟩
    · rintro (⟨hlt, hbω⟩ | ⟨heq, hbω⟩)
      · exact ⟨hlt.le, hbω⟩
      · exact ⟨heq.le, hbω⟩
  have hB : MeasurableSet B :=
    (measurableSet_eq_fun ha measurable_const).inter
      (measurableSet_lt measurable_const hb)
  have hBzero : μ B = 0 := by
    apply measure_mono_null (t := {ω | a ω = x})
    · intro ω hω
      exact hω.1
    · exact hAtom
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    intro ω hA hB
    exact (ne_of_lt hA.1) hB.1
  rw [hset, measure_union hdisj hB, hBzero, add_zero]

/-- The CDF recurrence has the paper's strict increment event if the lower
ordered statistic has zero boundary mass. -/
theorem orderedPair_sublevelMass_eq_add_strict {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (a b : Ω → ℝ) (ha : Measurable a) (hb : Measurable b)
    (x : ℝ) (horder : ∀ ω, a ω ≤ b ω)
    (hAtom : μ {ω | a ω = x} = 0) :
    μ {ω | a ω ≤ x} =
      μ {ω | b ω ≤ x} + μ {ω | a ω < x ∧ x < b ω} := by
  rw [orderedPair_sublevelMass_eq_add μ a b ha hb x horder]
  rw [orderedPair_increment_weak_eq_strict μ a b ha hb x hAtom]

end JinWishart
