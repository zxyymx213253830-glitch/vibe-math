import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Dimension of an intersection of subspaces

This is the finite-dimensional algebra step used in the indexed min-max argument for ordered
eigenvalues. The proof is the dimension formula for `U ⊔ V` and `U ⊓ V`, together with the fact
that the span `U ⊔ V` cannot have dimension larger than the ambient space.
-/

namespace JinWishart

open Module

variable {K E : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

/-- If the dimensions of two subspaces have sum larger than the ambient dimension, their
intersection has positive dimension. -/
theorem finrank_inf_pos_of_finrank_add_gt
    (U V : Submodule K E)
    (h : finrank K E < finrank K U + finrank K V) :
    0 < finrank K ↥(U ⊓ V) := by
  have hdim := U.finrank_sup_add_finrank_inf_eq V
  rw [← hdim] at h
  have hsup : finrank K ↥(U ⊔ V) ≤ finrank K E := Submodule.finrank_le _
  omega

/-- A positive-dimensional intersection contains a nonzero vector. -/
theorem exists_ne_zero_mem_of_finrank_inf_pos
    (U V : Submodule K E) (h : 0 < finrank K ↥(U ⊓ V)) :
    ∃ x : E, x ≠ 0 ∧ x ∈ U ∧ x ∈ V := by
  haveI : Nontrivial ↥(U ⊓ V) := (finrank_pos_iff).mp h
  obtain ⟨x, hx⟩ := exists_ne (0 : ↥(U ⊓ V))
  exact ⟨x.1, by simpa using hx, x.2.1, x.2.2⟩

/-- Direct nonzero-intersection form of `finrank_inf_pos_of_finrank_add_gt`. -/
theorem exists_ne_zero_mem_inf_of_finrank_add_gt
    (U V : Submodule K E)
    (h : finrank K E < finrank K U + finrank K V) :
    ∃ x : E, x ≠ 0 ∧ x ∈ U ∧ x ∈ V :=
  exists_ne_zero_mem_of_finrank_inf_pos U V
    (finrank_inf_pos_of_finrank_add_gt U V h)

end JinWishart
