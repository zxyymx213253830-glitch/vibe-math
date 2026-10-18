import JinWishartFormalization.FiniteSharedColumnCoordinates
import Mathlib.Data.Finset.Basic

/-! Exact Venn-region coordinates of two finite column sets.
Codex deterministic proofs; the construction supplies, rather than assumes,
the common/exclusive selector representation used in actual mixed moments.
-/
namespace JinWishart
noncomputable section

structure FiniteMinorOverlapModel {n : ℕ} (S T : Finset (Fin n)) where
  embedding : Fin (((S \ T).card + (T \ S).card) + (S ∩ T).card) → Fin n
  injective : Function.Injective embedding
  left : Fin ((S \ T).card + (S ∩ T).card) ≃ S
  right : Fin ((T \ S).card + (S ∩ T).card) ≃ T
  left_eq : embedding ∘ centralSharedPrefixSelection (S ∩ T).card
      (Fin.castAdd (T \ S).card) = Subtype.val ∘ left
  right_eq : embedding ∘ centralSharedPrefixSelection (S ∩ T).card
      (Fin.natAdd (S \ T).card) = Subtype.val ∘ right

def finiteMinorOverlapModel {n : ℕ} (S T : Finset (Fin n)) : FiniteMinorOverlapModel S T := by
  classical
  let C := S ∩ T
  let A := S \ T
  let B := T \ S
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    simp only [A, B, Finset.mem_sdiff] at hi hj
    exact hi.2 hj.1
  have hCA : Disjoint C A := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    simp only [A, C, Finset.mem_inter, Finset.mem_sdiff] at hi hj
    exact hj.2 hi.2
  have hCB : Disjoint C B := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    simp only [B, C, Finset.mem_inter, Finset.mem_sdiff] at hi hj
    exact hj.2 hi.1
  have hCD : Disjoint C (A ∪ B) := Finset.disjoint_union_right.mpr ⟨hCA,hCB⟩
  have hS : C ∪ A = S := by ext i; simp [C,A]; tauto
  have hT : C ∪ B = T := by ext i; simp [C,B]; tauto
  let eC : Fin C.card ≃ C := Fintype.equivOfCardEq (by simp)
  let eA : Fin A.card ≃ A := Fintype.equivOfCardEq (by simp)
  let eB : Fin B.card ≃ B := Fintype.equivOfCardEq (by simp)
  let eAB : Fin (A.card+B.card) ≃ (A ∪ B : Finset (Fin n)) :=
    finSumFinEquiv.symm.trans ((Equiv.sumCongr eA eB).trans (Equiv.Finset.union A B hAB))
  let eU : Fin ((A.card+B.card)+C.card) ≃ (C ∪ (A ∪ B) : Finset (Fin n)) :=
    (sharedCoordinates C.card (A.card+B.card)).trans
      ((Equiv.sumCongr eC eAB).trans (Equiv.Finset.union C (A ∪ B) hCD))
  let eS : Fin (A.card+C.card) ≃ S :=
    (sharedCoordinates C.card A.card).trans
      (((Equiv.sumCongr eC eA).trans (Equiv.Finset.union C A hCA)).trans
        (Set.equivOfEq (congrArg (fun U : Finset (Fin n) => (U : Set (Fin n))) hS)))
  let eT : Fin (B.card+C.card) ≃ T :=
    (sharedCoordinates C.card B.card).trans
      (((Equiv.sumCongr eC eB).trans (Equiv.Finset.union C B hCB)).trans
        (Set.equivOfEq (congrArg (fun U : Finset (Fin n) => (U : Set (Fin n))) hT)))
  refine ⟨fun i => (eU i).val, Subtype.val_injective.comp eU.injective, eS, eT, ?_, ?_⟩
  · funext i
    change (eU (centralSharedPrefixSelection C.card (Fin.castAdd B.card) i)).val = (eS i).val
    simp only [eU,eS,Equiv.trans_apply,centralSharedPrefixSelection_coordinates]
    rcases hj : (sharedCoordinates C.card A.card) i with j | j
    · simp [hj,Equiv.sumCongr_apply,Set.equivOfEq_apply] <;> rfl
    · simp [hj,eAB,Equiv.sumCongr_apply,Set.equivOfEq_apply] <;> rfl
  · funext i
    change (eU (centralSharedPrefixSelection C.card (Fin.natAdd A.card) i)).val = (eT i).val
    simp only [eU,eT,Equiv.trans_apply,centralSharedPrefixSelection_coordinates]
    rcases hj : (sharedCoordinates C.card B.card) i with j | j
    · simp [hj,Equiv.sumCongr_apply,Set.equivOfEq_apply] <;> rfl
    · simp [hj,eAB,Equiv.sumCongr_apply,Set.equivOfEq_apply] <;> rfl

theorem finiteMinorOverlap_left_card {n : ℕ} (S T : Finset (Fin n)) :
    (S \ T).card + (S ∩ T).card = S.card := by
  simpa using Fintype.card_congr (finiteMinorOverlapModel S T).left

theorem finiteMinorOverlap_right_card {n : ℕ} (S T : Finset (Fin n)) :
    (T \ S).card + (S ∩ T).card = T.card := by
  simpa using Fintype.card_congr (finiteMinorOverlapModel S T).right

end
end JinWishart
#print axioms JinWishart.finiteMinorOverlapModel
#print axioms JinWishart.finiteMinorOverlap_left_card
#print axioms JinWishart.finiteMinorOverlap_right_card
