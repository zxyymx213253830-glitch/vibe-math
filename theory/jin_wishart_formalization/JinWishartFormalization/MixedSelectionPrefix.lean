import JinWishartFormalization.MixedOrderedMinorProduct
import Mathlib.Order.Interval.Set.Monotone

/-! Codex. Seed 2026102901 exact selections and missing-index controls precede
this proof. Ordered selections containing every central index have that range
as their initial segment. This is not yet the arbitrary-selection determinant
or the mixed kernel positivity theorem. [需人工审查] Finite indexing. -/
open Function Set
namespace JinWishart
noncomputable section

theorem strictMono_fin_nat_index_le (n : ℕ) (g : Fin n → ℕ)
 (hg : StrictMono g) (i : Fin n) : i.val ≤ g i := by
 let F : ℕ → ℕ := fun t => if h : t < n then g ⟨t,h⟩ else 0
 have hF : StrictMonoOn F (Set.Iic i.val) := by
   intro a ha b hb hab
   change a ≤ i.val at ha
   change b ≤ i.val at hb
   have hi := i.isLt
   have han : a < n := by omega
   have hbn : b < n := by omega
   simp only [F,dif_pos han,dif_pos hbn]
   exact hg (show (⟨a,han⟩ : Fin n) < ⟨b,hbn⟩ from hab)
 have h := hF.Iic_id_le i.val le_rfl
 simpa [F,i.isLt] using h

theorem mixedSelection_sorted_prefix (p L : ℕ) (g : Fin (p+L) → ℕ)
 (hg : StrictMono g) (hseen : ∀ a : Fin p, ∃ i, g i = a.val) :
 ∀ a : Fin p, g (Fin.castAdd L a) = a.val := by
 have h : ∀ (v : ℕ) (hv : v < p), g ⟨v, by omega⟩ = v := by
   intro v
   induction v using Nat.strong_induction_on with
   | h v ih =>
     intro hv
     obtain ⟨t,ht⟩ := hseen ⟨v,hv⟩
     change g t = v at ht
     have hlow := strictMono_fin_nat_index_le (p+L) g hg t
     have htv : t.val ≤ v := by omega
     by_cases hlt : t.val < v
     · have htval : t.val < p := by omega
       have he := ih t.val hlt htval
       have het : g t = t.val := by simpa using he
       omega
     · have heq : t = (⟨v, by omega⟩ : Fin (p+L)) := by
         apply Fin.ext
         change t.val = v
         omega
       simpa [heq] using ht
 intro a
 have heq : Fin.castAdd L a = (⟨a.val, by omega⟩ : Fin (p+L)) := Fin.ext rfl
 rw [heq]
 exact h a.val a.isLt

theorem mixedSelection_sorted_tail_ge (p L : ℕ) (g : Fin (p+L) → ℕ)
 (hg : StrictMono g) (i : Fin L) : p ≤ g (Fin.natAdd p i) := by
 have h := strictMono_fin_nat_index_le (p+L) g hg (Fin.natAdd p i)
 simp only [Fin.val_natAdd] at h
 omega

end
end JinWishart
#print axioms JinWishart.strictMono_fin_nat_index_le
#print axioms JinWishart.mixedSelection_sorted_prefix
#print axioms JinWishart.mixedSelection_sorted_tail_ge
