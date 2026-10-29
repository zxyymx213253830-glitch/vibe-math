import JinWishartFormalization.MixedSelectionPrefix
import Mathlib.Data.Finset.Sort

/-! Codex. Seed 2026102901 exact selection controls precede this proof.
An injective selection containing each central index can be sorted into the
central prefix and a strictly increasing tail. [需人工审查] Fin/Sum indexing. -/
open Matrix Finset Function
namespace JinWishart
noncomputable section

theorem mixedSelection_sorted (p L N : ℕ) (f : (Fin p ⊕ Fin L) → Fin N)
 (hf : Injective f) (hseen : ∀ a : Fin p, ∃ i, (f i).val = a.val) :
 ∃ (hpN : p ≤ N) (k : Fin L → Fin N) (σ : Equiv.Perm (Fin p ⊕ Fin L)),
   (∀ i, p ≤ (k i).val) ∧ StrictMono k ∧
   ∀ i, f i = mixedOrderedSelection p L N hpN k (σ i) := by
 let e := finSumFinEquiv (m := p) (n := L)
 let f' : Fin (p+L) → Fin N := fun i => f (e.symm i)
 have hf' : Injective f' := hf.comp e.symm.injective
 have hnN : p+L ≤ N := by
   simpa using Fintype.card_le_of_injective f' hf'
 have hpN : p ≤ N := by omega
 let S := Finset.univ.image f'
 have hc : S.card = p+L := by simpa [S] using Finset.card_image_of_injective Finset.univ hf'
 let q : Fin (p+L) → S := fun i => ⟨f' i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
 have hq : Bijective q := by
   constructor
   · intro i j hij
     exact hf' (congrArg Subtype.val hij)
   · intro y
     obtain ⟨i,_,hi⟩ := Finset.mem_image.mp y.property
     exact ⟨i,Subtype.ext hi⟩
 let eqS := Equiv.ofBijective q hq
 let o := S.orderIsoOfFin hc
 let τ : Equiv.Perm (Fin (p+L)) := eqS.trans o.toEquiv.symm
 let g : Fin (p+L) → Fin N := fun i => o i
 have hg : StrictMono g := by
   intro i j hij
   exact o.strictMono hij
 have hfg (i : Fin (p+L)) : f' i = g (τ i) := by
   exact (congrArg Subtype.val (o.apply_symm_apply (eqS i))).symm
 have hgs : ∀ a : Fin p, ∃ i, (g i).val = a.val := by
   intro a
   obtain ⟨i,hi⟩ := hseen a
   refine ⟨τ (e i), ?_⟩
   have h := hfg (e i)
   dsimp [f'] at h
   rw [e.symm_apply_apply] at h
   rw [← h]
   exact hi
 have hgv : StrictMono (fun i => (g i).val) := fun i j hij => hg hij
 have hprefix := mixedSelection_sorted_prefix p L (fun i => (g i).val) hgv hgs
 let k : Fin L → Fin N := fun i => g (Fin.natAdd p i)
 have hkp : ∀ i, p ≤ (k i).val := by
   intro i
   exact mixedSelection_sorted_tail_ge p L (fun i => (g i).val) hgv i
 have hks : StrictMono k := hg.comp (Fin.strictMono_natAdd p)
 have hselect (i : Fin p ⊕ Fin L) :
   g (e i) = mixedOrderedSelection p L N hpN k i := by
   cases i with
   | inl i =>
     apply Fin.ext
     simpa [e,mixedOrderedSelection,finSumFinEquiv_apply_left] using hprefix i
   | inr i => rfl
 let σ : Equiv.Perm (Fin p ⊕ Fin L) := e.trans (τ.trans e.symm)
 refine ⟨hpN,k,σ,hkp,hks,?_⟩
 intro i
 have h := hfg (e i)
 dsimp [f'] at h
 rw [e.symm_apply_apply] at h
 rw [h,← hselect]
 simp [σ]

end
end JinWishart
#print axioms JinWishart.mixedSelection_sorted
