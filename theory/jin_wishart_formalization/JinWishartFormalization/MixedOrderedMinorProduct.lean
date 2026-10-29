import JinWishartFormalization.MixedCoefficientMinorZero
import Mathlib.Logic.Equiv.Fin.Basic

/-! Codex. Seed 2026102901 exact finite mixed-minor controls precede source.
This only handles an explicitly ordered surviving selection, not arbitrary
selections or the mixed-rank kernel determinant. [需人工审查] Fin/Sum indexing. -/
open Matrix Function
namespace JinWishart
noncomputable section

def mixedOrderedDegree (p L N : ℕ) (k : Fin L → Fin N) (i : Fin (p+L)) : ℕ :=
 if h : i.val < p then i.val else (k ⟨i.val-p, by omega⟩).val

theorem mixedOrderedDegree_strictMono (p L N : ℕ) (k : Fin L → Fin N)
 (hkp : ∀ i, p ≤ (k i).val) (hks : StrictMono k) :
 StrictMono (mixedOrderedDegree p L N k) := by
 intro i j hij
 have hijv : i.val < j.val := hij
 by_cases hi : i.val < p <;> by_cases hj : j.val < p
 · simp [mixedOrderedDegree,hi,hj,hijv]
 · simp only [mixedOrderedDegree, dif_pos hi, dif_neg hj]
   have h := hkp ⟨j.val-p, by omega⟩
   omega
 · omega
 · simp only [mixedOrderedDegree,dif_neg hi,dif_neg hj]
   apply hks
   change i.val-p < j.val-p
   omega

theorem mixedOrderedDegree_selection (p L N : ℕ) (hpN : p ≤ N) (k : Fin L → Fin N)
 (i : Fin p ⊕ Fin L) :
 mixedOrderedDegree p L N k (finSumFinEquiv i) =
   (mixedOrderedSelection p L N hpN k i).val := by
 cases i with
 | inl i => simp [mixedOrderedDegree,mixedOrderedSelection,finSumFinEquiv_apply_left]
 | inr i => simp [mixedOrderedDegree,mixedOrderedSelection,finSumFinEquiv_apply_right]

theorem mixedOrderedMinorProduct_pos (p L N : ℕ) (hpN : p ≤ N)
 (x : Fin (p+L) → ℝ) (lambda : Fin L → ℝ) (w : ℕ → ℝ)
 (k : Fin L → Fin N) (hkp : ∀ i, p ≤ (k i).val) (hks : StrictMono k)
 (hx : StrictMono x) (hxp : ∀ i, 0 < x i) (hl : StrictMono lambda)
 (hlp : ∀ i, 0 < lambda i) (hw : ∀ i, 0 < w ((k i).val)) :
 0 < (Matrix.of (fun i j : Fin p ⊕ Fin L =>
   x (finSumFinEquiv i) ^ (mixedOrderedSelection p L N hpN k j).val)).det *
   ((mixedKernelCoefficient p L N lambda w).submatrix
      (mixedOrderedSelection p L N hpN k) id).det := by
 let e := finSumFinEquiv (m := p) (n := L)
 let A : Matrix (Fin (p+L)) (Fin (p+L)) ℝ :=
   Matrix.of (fun i j => x i ^ mixedOrderedDegree p L N k j)
 have hA : (Matrix.of (fun i j : Fin p ⊕ Fin L =>
     x (e i) ^ (mixedOrderedSelection p L N hpN k j).val)) =
       A.submatrix e e := by
   ext i j
   change x (e i) ^ (mixedOrderedSelection p L N hpN k j).val =
     x (e i) ^ mixedOrderedDegree p L N k (e j)
   rw [mixedOrderedDegree_selection]
 rw [hA,Matrix.det_submatrix_equiv_self]
 have hdet : 0 < A.det :=
   generalizedMonomialVandermonde_det_pos (p+L) (mixedOrderedDegree p L N k)
     x (mixedOrderedDegree_strictMono p L N k hkp hks) hx hxp
 exact mul_pos hdet (mixedCoefficient_ordered_det_pos p L N hpN lambda w k hkp hks hl hlp hw)

end
end JinWishart
#print axioms JinWishart.mixedOrderedDegree_strictMono
#print axioms JinWishart.mixedOrderedDegree_selection
#print axioms JinWishart.mixedOrderedMinorProduct_pos
