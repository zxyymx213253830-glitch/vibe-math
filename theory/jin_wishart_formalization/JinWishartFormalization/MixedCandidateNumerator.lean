import JinWishartFormalization.InfiniteMixedNoncentralKernel
import Mathlib.Data.Finset.Sort

/-! Codex. Seed 2026103001:306 mixed-rank symmetry controls precede source.
Formula-side numerator only; no normalization or actual law is asserted.
[需人工审查] Sorting, indices, measure and eventual paper mapping. -/
open Matrix Finset Function
namespace JinWishart
noncomputable section

def mixedSeriesNumerator (p L q : ℕ) (lambda : Fin L → ℝ)
 (x : Fin (p+L) → ℝ) : ℝ :=
 (Matrix.vandermonde x).det*(infiniteMixedKernel p L q x lambda).det

theorem mixedSeriesNumerator_permute (p L q : ℕ) (lambda : Fin L → ℝ)
 (x : Fin (p+L) → ℝ) (σ : Equiv.Perm (Fin (p+L))) :
 mixedSeriesNumerator p L q lambda (fun i => x (σ i)) = mixedSeriesNumerator p L q lambda x := by
 have hv : Matrix.vandermonde (fun i => x (σ i)) = (Matrix.vandermonde x).submatrix σ id := rfl
 have hk : infiniteMixedKernel p L q (fun i => x (σ i)) lambda =
     (infiniteMixedKernel p L q x lambda).submatrix σ id := rfl
 simp only [mixedSeriesNumerator,hv,hk,Matrix.det_permute]
 have hs : ((Equiv.Perm.sign σ : ℤ) : ℝ)*((Equiv.Perm.sign σ : ℤ) : ℝ) = 1 := by
   exact_mod_cast Int.isUnit_mul_self (Equiv.Perm.sign σ).isUnit
 calc
   _ = (((Equiv.Perm.sign σ : ℤ) : ℝ)*((Equiv.Perm.sign σ : ℤ) : ℝ))*
       ((Matrix.vandermonde x).det*(infiniteMixedKernel p L q x lambda).det) := by ring
   _ = _ := by rw [hs,one_mul]

private theorem sorted_nodes (n : ℕ) (x : Fin n → ℝ) (hx : Injective x) :
 ∃ (g : Fin n → ℝ) (σ : Equiv.Perm (Fin n)), StrictMono g ∧ ∀ i, x i = g (σ i) := by
 let S := Finset.univ.image x
 have hc : S.card = n := by simpa [S] using Finset.card_image_of_injective Finset.univ hx
 let f : Fin n → S := fun i => ⟨x i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
 have hf : Bijective f := by
   constructor
   · intro i j hij
     exact hx (congrArg Subtype.val hij)
   · intro y
     obtain ⟨i,_,hi⟩ := Finset.mem_image.mp y.property
     exact ⟨i,Subtype.ext hi⟩
 let e := Equiv.ofBijective f hf
 let o := S.orderIsoOfFin hc
 refine ⟨fun i => (o i : ℝ),e.trans o.toEquiv.symm,?_,?_⟩
 · intro i j hij
   exact o.strictMono hij
 · intro i
   exact (congrArg Subtype.val (o.apply_symm_apply (e i))).symm

theorem mixedSeriesNumerator_pos (p L q : ℕ) (lambda : Fin L → ℝ)
 (x : Fin (p+L) → ℝ) (hl : StrictMono lambda) (hlp : ∀ i, 0 < lambda i)
 (hx : Injective x) (hxp : ∀ i, 0 < x i) : 0 < mixedSeriesNumerator p L q lambda x := by
 obtain ⟨g,σ,hg,hxg⟩ := sorted_nodes (p+L) x hx
 have hp (i : Fin (p+L)) : 0 < g i := by
   have h := hxp (σ.symm i)
   rw [hxg,σ.apply_symm_apply] at h
   exact h
 have he : x = fun i => g (σ i) := funext hxg
 rw [he,mixedSeriesNumerator_permute]
 have hv : 0 < (Matrix.vandermonde g).det := by
   convert generalizedMonomialVandermonde_det_pos (p+L) (fun i : Fin (p+L) => i.val) g
     (by intro i j hij; exact hij) hg hp using 1 <;> rfl
 exact mul_pos hv (infiniteMixedKernel_det_pos p L q g lambda hg hp hl hlp)

theorem mixedSeriesNumerator_nonneg (p L q : ℕ) (lambda : Fin L → ℝ)
 (x : Fin (p+L) → ℝ) (hl : StrictMono lambda) (hlp : ∀ i, 0 < lambda i)
 (hxp : ∀ i, 0 < x i) : 0 ≤ mixedSeriesNumerator p L q lambda x := by
 by_cases hx : Injective x
 · exact (mixedSeriesNumerator_pos p L q lambda x hl hlp hx hxp).le
 · simp only [Injective] at hx
   push_neg at hx
   obtain ⟨i,j,hij,hne⟩ := hx
   have hv : (Matrix.vandermonde x).det = 0 := by
     apply Matrix.det_zero_of_row_eq hne
     funext k
     change x i ^ k.val = x j ^ k.val
     rw [hij]
   rw [mixedSeriesNumerator,hv,zero_mul]

end
end JinWishart
#print axioms JinWishart.mixedSeriesNumerator_permute
#print axioms JinWishart.mixedSeriesNumerator_pos
#print axioms JinWishart.mixedSeriesNumerator_nonneg
