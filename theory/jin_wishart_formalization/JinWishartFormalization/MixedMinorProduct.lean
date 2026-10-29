import JinWishartFormalization.MixedSelectionSorting

/-! Codex. Seed 2026102901 exact all-selection sign controls precede source.
The product is nonnegative for arbitrary selections, including missing central
indices and repeated selections. No Cauchy--Binet sum or probability law is
asserted here. [需人工审查] Simultaneous permutation and index orientation. -/
open Matrix Finset Function
namespace JinWishart
noncomputable section

def mixedSelectionMinorProduct (p L N : ℕ) (x : Fin (p+L) → ℝ)
 (lambda : Fin L → ℝ) (w : ℕ → ℝ) (f : (Fin p ⊕ Fin L) → Fin N) : ℝ :=
 (Matrix.of (fun i j : Fin p ⊕ Fin L => x (finSumFinEquiv i) ^ (f j).val)).det *
   ((mixedKernelCoefficient p L N lambda w).submatrix f id).det

theorem mixedSelectionMinorProduct_pos (p L N : ℕ) (x : Fin (p+L) → ℝ)
 (lambda : Fin L → ℝ) (w : ℕ → ℝ) (f : (Fin p ⊕ Fin L) → Fin N)
 (hf : Injective f) (hseen : ∀ a : Fin p, ∃ i, (f i).val = a.val)
 (hx : StrictMono x) (hxp : ∀ i, 0 < x i) (hl : StrictMono lambda)
 (hlp : ∀ j, 0 < lambda j) (hw : ∀ m, 0 < w m) :
 0 < mixedSelectionMinorProduct p L N x lambda w f := by
 obtain ⟨hpN,k,σ,hkp,hks,hfσ⟩ := mixedSelection_sorted p L N f hf hseen
 let s := mixedOrderedSelection p L N hpN k
 let A : Matrix (Fin p ⊕ Fin L) (Fin p ⊕ Fin L) ℝ :=
   Matrix.of (fun i j => x (finSumFinEquiv i) ^ (s j).val)
 let B := (mixedKernelCoefficient p L N lambda w).submatrix s id
 have hA : (Matrix.of (fun i j : Fin p ⊕ Fin L =>
     x (finSumFinEquiv i) ^ (f j).val)) = A.submatrix id σ := by
   ext i j
   change x (finSumFinEquiv i) ^ (f j).val = x (finSumFinEquiv i) ^ (s (σ j)).val
   rw [hfσ]
 have hB : (mixedKernelCoefficient p L N lambda w).submatrix f id =
     B.submatrix σ id := by
   ext i j
   change mixedKernelCoefficient p L N lambda w (f i) j =
     mixedKernelCoefficient p L N lambda w (s (σ i)) j
   rw [hfσ]
 unfold mixedSelectionMinorProduct
 rw [hA,hB,Matrix.det_permute',Matrix.det_permute]
 have hs : ((Equiv.Perm.sign σ : ℤ) : ℝ)*((Equiv.Perm.sign σ : ℤ) : ℝ) = 1 := by
   exact_mod_cast Int.isUnit_mul_self (Equiv.Perm.sign σ).isUnit
 have hp : 0 < A.det * B.det :=
   mixedOrderedMinorProduct_pos p L N hpN x lambda w k hkp hks hx hxp hl hlp (fun i => hw _)
 calc
   0 < A.det * B.det := hp
   _ = (((Equiv.Perm.sign σ : ℤ) : ℝ)*((Equiv.Perm.sign σ : ℤ) : ℝ)) *
       (A.det * B.det) := by rw [hs,one_mul]
   _ = (((Equiv.Perm.sign σ : ℤ) : ℝ)*A.det)*
       (((Equiv.Perm.sign σ : ℤ) : ℝ)*B.det) := by ring

theorem mixedSelectionMinorProduct_nonneg (p L N : ℕ) (x : Fin (p+L) → ℝ)
 (lambda : Fin L → ℝ) (w : ℕ → ℝ) (f : (Fin p ⊕ Fin L) → Fin N)
 (hx : StrictMono x) (hxp : ∀ i, 0 < x i) (hl : StrictMono lambda)
 (hlp : ∀ j, 0 < lambda j) (hw : ∀ m, 0 < w m) :
 0 ≤ mixedSelectionMinorProduct p L N x lambda w f := by
 by_cases hf : Injective f
 · by_cases hs : ∀ a : Fin p, ∃ i, (f i).val = a.val
   · exact (mixedSelectionMinorProduct_pos p L N x lambda w f hf hs hx hxp hl hlp hw).le
   · push_neg at hs
     obtain ⟨a,ha⟩ := hs
     unfold mixedSelectionMinorProduct
     rw [mixedCoefficientMinor_zero_of_missing p L N lambda w f a ha, mul_zero]
 · unfold mixedSelectionMinorProduct
   rw [mixedCoefficientMinor_zero_of_repeated p L N lambda w f hf, mul_zero]

end
end JinWishart
#print axioms JinWishart.mixedSelectionMinorProduct_pos
#print axioms JinWishart.mixedSelectionMinorProduct_nonneg
