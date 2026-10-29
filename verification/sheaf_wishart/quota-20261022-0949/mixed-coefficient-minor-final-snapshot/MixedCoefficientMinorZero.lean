import JinWishartFormalization.ZeroConfluentVandermondePos
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Codex. The seed 2026102901 exact mixed-kernel controls precede this
algebraic lemma. Central columns are coefficient selectors, not derivatives.
This does not assert positivity of all surviving minors or an actual law.
[需人工审查] Central-column and finite selection indexing. -/
open Matrix Function
namespace JinWishart
noncomputable section

def mixedKernelCoefficient (p L N : ℕ) (lambda : Fin L → ℝ) (w : ℕ → ℝ) :
 Matrix (Fin N) (Fin p ⊕ Fin L) ℝ :=
 fun m j => match j with
 | Sum.inl a => if m.val = a.val then 1 else 0
 | Sum.inr b => w m.val * lambda b ^ m.val

theorem mixedCoefficientMinor_zero_of_missing (p L N : ℕ)
 (lambda : Fin L → ℝ) (w : ℕ → ℝ) (f : (Fin p ⊕ Fin L) → Fin N)
 (a : Fin p) (hmissing : ∀ i, (f i).val ≠ a.val) :
 ((mixedKernelCoefficient p L N lambda w).submatrix f id).det = 0 := by
 apply Matrix.det_eq_zero_of_column_eq_zero (Sum.inl a)
 intro i
 simp [mixedKernelCoefficient,hmissing i]

theorem mixedCoefficientMinor_zero_of_repeated (p L N : ℕ)
 (lambda : Fin L → ℝ) (w : ℕ → ℝ) (f : (Fin p ⊕ Fin L) → Fin N)
 (hf : ¬ Injective f) :
 ((mixedKernelCoefficient p L N lambda w).submatrix f id).det = 0 := by
 simp only [Injective] at hf
 push_neg at hf
 obtain ⟨i,j,hij,hne⟩ := hf
 apply Matrix.det_zero_of_row_eq hne
 funext k
 change mixedKernelCoefficient p L N lambda w (f i) k =
   mixedKernelCoefficient p L N lambda w (f j) k
 rw [hij]

theorem mixedCoefficient_canonical_eq (p L : ℕ) (lambda : Fin L → ℝ) (w : ℕ → ℝ) :
 (mixedKernelCoefficient p L (p+L) lambda w).submatrix
   (finSumFinEquiv (m := p) (n := L)) id =
     weightedZeroConfluentVandermonde p L lambda w := by
 ext i j
 cases i with
 | inl i =>
   cases j with
   | inl j =>
     simp [mixedKernelCoefficient,weightedZeroConfluentVandermonde,
       Matrix.fromBlocks,Matrix.one_apply,finSumFinEquiv_apply_left,Fin.ext_iff]
     split_ifs <;> simp_all [Fin.ext_iff]
   | inr j =>
     simp [mixedKernelCoefficient,weightedZeroConfluentVandermonde,
       Matrix.fromBlocks,finSumFinEquiv_apply_left]
 | inr i =>
   cases j with
   | inl j =>
     have h : p + i.val ≠ j.val := by omega
     simp [mixedKernelCoefficient,weightedZeroConfluentVandermonde,
       Matrix.fromBlocks,finSumFinEquiv_apply_right,h]
   | inr j =>
     simp [mixedKernelCoefficient,weightedZeroConfluentVandermonde,
       Matrix.fromBlocks,finSumFinEquiv_apply_right]

theorem mixedCoefficient_canonical_det_pos (p L : ℕ) (lambda : Fin L → ℝ)
 (w : ℕ → ℝ) (hl : StrictMono lambda) (hp : ∀ j, 0 < lambda j)
 (hw : ∀ i : Fin L, 0 < w (p+i.val)) :
 0 < ((mixedKernelCoefficient p L (p+L) lambda w).submatrix
   (finSumFinEquiv (m := p) (n := L)) id).det := by
 rw [mixedCoefficient_canonical_eq]
 exact weightedZeroConfluentVandermonde_det_pos p L lambda w hl hp hw

def mixedOrderedSelection (p L N : ℕ) (hpN : p ≤ N) (k : Fin L → Fin N) :
 (Fin p ⊕ Fin L) → Fin N
 | Sum.inl i => Fin.castLE hpN i
 | Sum.inr i => k i

theorem mixedCoefficient_ordered_eq (p L N : ℕ) (hpN : p ≤ N)
 (lambda : Fin L → ℝ) (w : ℕ → ℝ) (k : Fin L → Fin N)
 (hk : ∀ i, p ≤ (k i).val) :
 (mixedKernelCoefficient p L N lambda w).submatrix
   (mixedOrderedSelection p L N hpN k) id =
     weightedGeneralizedConfluent p L (fun i => (k i).val) lambda w := by
 ext i j
 cases i with
 | inl i =>
   cases j with
   | inl j =>
     simp [mixedKernelCoefficient,mixedOrderedSelection,weightedGeneralizedConfluent,
       Matrix.fromBlocks,Matrix.one_apply,Fin.ext_iff]
     split_ifs <;> simp_all [Fin.ext_iff]
   | inr j =>
     simp [mixedKernelCoefficient,mixedOrderedSelection,weightedGeneralizedConfluent,
       Matrix.fromBlocks]
 | inr i =>
   cases j with
   | inl j =>
     have h : (k i).val ≠ j.val := by have := hk i; omega
     simp [mixedKernelCoefficient,mixedOrderedSelection,weightedGeneralizedConfluent,
       Matrix.fromBlocks,h]
   | inr j =>
     simp [mixedKernelCoefficient,mixedOrderedSelection,weightedGeneralizedConfluent,
       Matrix.fromBlocks]

theorem mixedCoefficient_ordered_det_pos (p L N : ℕ) (hpN : p ≤ N)
 (lambda : Fin L → ℝ) (w : ℕ → ℝ) (k : Fin L → Fin N)
 (hkp : ∀ i, p ≤ (k i).val) (hks : StrictMono k) (hl : StrictMono lambda)
 (hp : ∀ j, 0 < lambda j) (hw : ∀ i, 0 < w ((k i).val)) :
 0 < ((mixedKernelCoefficient p L N lambda w).submatrix
   (mixedOrderedSelection p L N hpN k) id).det := by
 rw [mixedCoefficient_ordered_eq p L N hpN lambda w k hkp]
 apply weightedGeneralizedConfluent_det_pos p L (fun i => (k i).val) lambda w
 · intro i j hij
   exact hks hij
 · exact hl
 · exact hp
 · exact hw

end
end JinWishart
#print axioms JinWishart.mixedCoefficientMinor_zero_of_missing
#print axioms JinWishart.mixedCoefficientMinor_zero_of_repeated
#print axioms JinWishart.mixedCoefficient_canonical_eq
#print axioms JinWishart.mixedCoefficient_canonical_det_pos
#print axioms JinWishart.mixedCoefficient_ordered_eq
#print axioms JinWishart.mixedCoefficient_ordered_det_pos
