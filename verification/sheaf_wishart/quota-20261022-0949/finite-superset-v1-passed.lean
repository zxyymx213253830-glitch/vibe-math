import JinWishartFormalization.FiniteSubsetPairGrouping
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-! Codex. Seed2026102504 exact controls precede source. Finite weighted
superset identity, no integration or stochastic model.
[需人工审查] Later overlap-kernel and Wishart interpretation. -/
open Finset
namespace JinWishart
noncomputable section

private theorem binomial_superset_weight_sum (n u : ℕ) (hu : u≤n) :
    (∑ b ∈ range (n-u+1), ((n-u).choose b : ℝ)/
      (((n+1 : ℕ) : ℝ)*(n.choose (u+b) : ℝ))) = 1/((u+1 : ℕ) : ℝ) := by
  have hc : (n.choose u : ℝ)≠0 := by exact_mod_cast (Nat.choose_pos hu).ne'
  have hn : ((n+1 : ℕ) : ℝ)≠0 := by positivity
  have hu0 : ((u+1 : ℕ) : ℝ)≠0 := by positivity
  have hterm (b : ℕ) (hb : b∈range (n-u+1)) :
      ((n-u).choose b : ℝ)/(((n+1 : ℕ) : ℝ)*(n.choose (u+b) : ℝ)) =
        ((b+u).choose u : ℝ)/(((n+1 : ℕ) : ℝ)*(n.choose u : ℝ)) := by
    have hb0 : b≤n-u := Nat.le_of_lt_succ (mem_range.mp hb)
    have hk : u+b≤n := by omega
    have hk0 : (n.choose (u+b) : ℝ)≠0 := by exact_mod_cast (Nat.choose_pos hk).ne'
    have h := Nat.choose_mul (n := n) (k := u+b) (s := u) (by omega)
    simp only [Nat.add_sub_cancel_left] at h
    have hr : (n.choose (u+b) : ℝ)*((b+u).choose u : ℝ)=
        (n.choose u : ℝ)*((n-u).choose b : ℝ) := by
      exact_mod_cast (by simpa [Nat.add_comm] using h)
    apply (div_eq_div_iff (mul_ne_zero hn hk0) (mul_ne_zero hn hc)).2
    nlinarith [hr]
  rw [sum_congr rfl hterm,← sum_div]
  have hs : (∑ b ∈ range (n-u+1),((b+u).choose u : ℝ))=((n+1).choose (u+1) : ℝ) := by
    exact_mod_cast (by simpa [Nat.sub_add_cancel hu] using Nat.sum_range_add_choose (n-u) u)
  rw [hs]
  have h := Nat.add_one_mul_choose_eq n u
  have hr : ((n+1 : ℕ) : ℝ)*(n.choose u : ℝ)=
      ((n+1).choose (u+1) : ℝ)*((u+1 : ℕ) : ℝ) := by exact_mod_cast h
  apply (div_eq_div_iff (mul_ne_zero hn hc) hu0).2
  nlinarith [hr]

theorem finiteSupersetKernel_sum (n : ℕ) (U : Finset (Fin n)) :
    (∑ R : Finset (Fin n), if U⊆R then
      1/(((n+1 : ℕ) : ℝ)*(n.choose R.card : ℝ)) else 0) =
        1/((U.card+1 : ℕ) : ℝ) := by
  classical
  have hsub (C : Finset U) (D : Finset {i : Fin n // i∉U}) :
      U⊆(finsetPartitionEquiv U).symm (C,D) ↔ C=univ := by
    constructor
    · intro h
      have hc := congrArg Finset.card (Finset.inter_eq_left.mpr h)
      rw [finsetPartitionEquiv_inter_card] at hc
      exact Finset.eq_of_subset_of_card_le (subset_univ C) (by simpa using hc.ge)
    · rintro rfl
      have hc : (U ∩ (finsetPartitionEquiv U).symm (univ,D)).card=U.card := by
        rw [finsetPartitionEquiv_inter_card]
        simp
      have he : U ∩ (finsetPartitionEquiv U).symm (univ,D)=U :=
        Finset.eq_of_subset_of_card_le inter_subset_left hc.ge
      exact Finset.inter_eq_left.mp he
  have h := Equiv.sum_comp (finsetPartitionEquiv U).symm
    (fun R : Finset (Fin n) => if U⊆R then 1/(((n+1 : ℕ) : ℝ)*(n.choose R.card : ℝ)) else 0)
  rw [← h]
  simp only [Function.comp_apply,Fintype.sum_prod_type]
  rw [sum_comm]
  simp only [hsub,finsetPartitionEquiv_symm_card]
  simp only [sum_ite_eq',mem_univ,if_true,card_univ,Fintype.card_coe]
  have hd := sum_finsets_card_fintype (α := {i : Fin n // i∉U})
    (fun b => 1/(((n+1 : ℕ) : ℝ)*(n.choose (U.card+b) : ℝ)))
  rw [hd]
  simp only [Fintype.card_subtype_compl,Fintype.card_fin,Fintype.card_coe]
  simp only [mul_one_div]
  apply binomial_superset_weight_sum
  simpa using card_le_card (subset_univ U)

end
end JinWishart
#print axioms JinWishart.finiteSupersetKernel_sum
