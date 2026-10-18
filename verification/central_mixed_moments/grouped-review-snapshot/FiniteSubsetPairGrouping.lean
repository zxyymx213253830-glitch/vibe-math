import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Sum
import Mathlib.Logic.Equiv.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Fintype.Card

/-! Cardinality grouping of pair-of-subsets statistics.
Codex deterministic proofs, following exact finite enumeration controls.
-/
open scoped BigOperators
namespace JinWishart
noncomputable section

def finsetPartitionEquiv {α : Type*} [DecidableEq α] (S : Finset α) :
    Finset α ≃ Finset S × Finset {i : α // i ∉ S} :=
  (Equiv.finsetCongr (Equiv.sumCompl (fun i => i ∈ S)).symm).trans Finset.sumEquiv.toEquiv

theorem finsetPartitionEquiv_symm {α : Type*} [DecidableEq α] (S : Finset α)
    (C : Finset S) (D : Finset {i : α // i ∉ S}) :
    (finsetPartitionEquiv S).symm (C,D) =
      (C.disjSum D).map (Equiv.sumCompl (fun i => i ∈ S)).toEmbedding := by rfl

theorem finsetPartitionEquiv_symm_card {α : Type*} [DecidableEq α] (S : Finset α)
    (C : Finset S) (D : Finset {i : α // i ∉ S}) :
    ((finsetPartitionEquiv S).symm (C,D)).card = C.card+D.card := by
  rw [finsetPartitionEquiv_symm,Finset.card_map,Finset.card_disjSum]

theorem finsetPartitionEquiv_inter_card {α : Type*} [DecidableEq α] (S : Finset α)
    (C : Finset S) (D : Finset {i : α // i ∉ S}) :
    (S ∩ (finsetPartitionEquiv S).symm (C,D)).card = C.card := by
  classical
  have hI : S ∩ (finsetPartitionEquiv S).symm (C,D) =
      C.map (Function.Embedding.subtype (fun i => i ∈ S)) := by
    rw [finsetPartitionEquiv_symm]
    ext i
    constructor
    · intro hi
      obtain ⟨a,ha,he⟩ := Finset.mem_map.mp (Finset.mem_inter.mp hi).2
      rcases a with a | a
      · exact Finset.mem_map.mpr ⟨a,by simpa using ha,he⟩
      · change a.val=i at he
        have hs : a.val ∈ S := he.symm ▸ (Finset.mem_inter.mp hi).1
        exact False.elim (a.property hs)
    · intro hi
      obtain ⟨a,ha,he⟩ := Finset.mem_map.mp hi
      change a.val=i at he
      subst i
      exact Finset.mem_inter.mpr ⟨a.property,
        Finset.mem_map.mpr ⟨Sum.inl a,by simpa using ha,rfl⟩⟩
  rw [hI,Finset.card_map]

theorem sum_finsets_card_fintype {α : Type*} [Fintype α] (f : ℕ → ℝ) :
    (∑ S : Finset α, f S.card) =
      ∑ k ∈ Finset.range (Fintype.card α+1), (Fintype.card α).choose k * f k := by
  classical
  rw [← Finset.powerset_univ,Finset.sum_powerset]
  simp_rw [Finset.sum_powersetCard]
  simp only [Finset.card_univ,nsmul_eq_mul]

theorem sum_finsets_intersection_card (n : ℕ) (S : Finset (Fin n)) (f : ℕ → ℕ → ℝ) :
    (∑ T : Finset (Fin n), f T.card (S ∩ T).card) =
      ∑ c ∈ Finset.range (S.card+1), ∑ b ∈ Finset.range (n-S.card+1),
        (S.card.choose c : ℝ) * ((n-S.card).choose b : ℝ) * f (c+b) c := by
  classical
  have h := Equiv.sum_comp (finsetPartitionEquiv S).symm
    (fun T : Finset (Fin n) => f T.card (S ∩ T).card)
  simp only [Function.comp_apply,Fintype.sum_prod_type,
    finsetPartitionEquiv_symm_card,finsetPartitionEquiv_inter_card] at h
  have hC := sum_finsets_card_fintype (α := S)
    (fun c => ∑ D : Finset {i : Fin n // i ∉ S}, f (c+D.card) c)
  rw [← h,hC]
  simp only [Fintype.card_coe]
  apply Finset.sum_congr rfl
  intro c _
  have hD := sum_finsets_card_fintype (α := {i : Fin n // i ∉ S}) (fun b => f (c+b) c)
  rw [hD]
  simp only [Fintype.card_subtype_compl,Fintype.card_fin,Fintype.card_coe]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- A double sum over 4^n subset pairs reduces to three bounded cardinalities. -/
theorem sum_finsets_pair_cardinalities (n : ℕ) (f : ℕ → ℕ → ℕ → ℝ) :
    (∑ S : Finset (Fin n), ∑ T : Finset (Fin n), f S.card T.card (S ∩ T).card) =
      ∑ a ∈ Finset.range (n+1), ∑ c ∈ Finset.range (a+1),
        ∑ b ∈ Finset.range (n-a+1),
          (n.choose a : ℝ) * (a.choose c : ℝ) * ((n-a).choose b : ℝ) * f a (c+b) c := by
  classical
  simp_rw [sum_finsets_intersection_card]
  have hG := sum_finsets_card_fintype (α := Fin n)
    (fun a => ∑ c ∈ Finset.range (a+1), ∑ b ∈ Finset.range (n-a+1),
      (a.choose c : ℝ) * ((n-a).choose b : ℝ) * f a (c+b) c)
  rw [hG]
  simp only [Fintype.card_fin]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

end
end JinWishart
#print axioms JinWishart.finsetPartitionEquiv_symm
#print axioms JinWishart.finsetPartitionEquiv_symm_card
#print axioms JinWishart.finsetPartitionEquiv_inter_card
#print axioms JinWishart.sum_finsets_card_fintype
#print axioms JinWishart.sum_finsets_intersection_card
#print axioms JinWishart.sum_finsets_pair_cardinalities
