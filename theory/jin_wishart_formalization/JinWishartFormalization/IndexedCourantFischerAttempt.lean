import JinWishartFormalization.SubspaceIntersectionFinrank
import JinWishartFormalization.OrderedEigenvalueWeyl
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Finite-dimensional ingredients for an indexed Courant--Fischer theorem

This file records a reusable finite-dimensional basis-span lemma. Together with
`SubspaceIntersectionFinrank`, it provides the dimension bookkeeping for the head/tail subspaces
in the Courant--Fischer proof. The remaining step is to establish Rayleigh quotient bounds on
these subspaces from the support of coordinates in the eigenbasis; that weighted-average estimate
is not supplied directly by the pinned Mathlib API.
-/

namespace JinWishart

open Module Submodule

variable {K E ι : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]
  [FiniteDimensional K E]

/-- The span of a subset of basis vectors has dimension equal to the cardinality of its index
subtype. This is the dimension calculation for spectral head/tail subspaces. -/
theorem finrank_span_basis_image_eq_card
    (b : Basis ι K E) (s : Set ι) [Fintype s] :
    finrank K ↥(span K (b '' s)) = Fintype.card s := by
  have hlin : LinearIndependent K (fun j : s => b j.1) :=
    b.linearIndependent.comp Subtype.val Subtype.val_injective
  have hrange : Set.range (fun j : s => b j.1) = b '' s := by
    ext x
    simp
  rw [← hrange]
  exact finrank_span_eq_card hlin

end JinWishart
