import JinWishartFormalization.ZeroConfluentVandermonde
import JinWishartFormalization.GeneralizedMonomialVandermondePos

/-! Codex. Seed 2026102901 exact mixed-kernel controls precede this proof.
The central columns encode coefficient conditions, not derivatives. This is a
deterministic lower-minor building block, not a mixed-rank Wishart law.
[需人工审查] Sum-index orientation and connection to the physical model. -/
open Matrix Finset
namespace JinWishart
noncomputable section

theorem zeroConfluentVandermonde_det_pos (p L : ℕ) (lambda : Fin L → ℝ)
 (hl : StrictMono lambda) (hp : ∀ j, 0 < lambda j) :
 0 < (zeroConfluentVandermonde p L lambda).det := by
 rw [zeroConfluentVandermonde_det]
 have hv : 0 < (Matrix.vandermonde lambda).det := by
   convert generalizedMonomialVandermonde_det_pos L (fun i : Fin L => i.val)
     lambda (by intro i j hij; exact hij) hl hp using 1 <;> rfl
 exact mul_pos (Finset.prod_pos (fun j _ => pow_pos (hp j) p)) hv

def weightedZeroConfluentVandermonde (p L : ℕ) (lambda : Fin L → ℝ)
 (w : ℕ → ℝ) : Matrix (Fin p ⊕ Fin L) (Fin p ⊕ Fin L) ℝ :=
 Matrix.fromBlocks 1 (Matrix.of (fun i j => w i.val * lambda j ^ i.val)) 0
   (Matrix.of (fun i j => w (p+i.val) * lambda j ^ (p+i.val)))

theorem weightedZeroConfluentVandermonde_det_pos (p L : ℕ) (lambda : Fin L → ℝ)
 (w : ℕ → ℝ) (hl : StrictMono lambda) (hp : ∀ j, 0 < lambda j)
 (hw : ∀ i : Fin L, 0 < w (p+i.val)) :
 0 < (weightedZeroConfluentVandermonde p L lambda w).det := by
 unfold weightedZeroConfluentVandermonde
 rw [Matrix.det_fromBlocks_zero₂₁,Matrix.det_one,one_mul]
 have hfactor : (Matrix.of (fun i j : Fin L =>
     w (p+i.val) * lambda j ^ (p+i.val))).det =
     (∏ i : Fin L, w (p+i.val)) *
       (Matrix.of (fun i j : Fin L => lambda j ^ (p+i.val))).det := by
   convert Matrix.det_mul_column (fun i : Fin L => w (p+i.val))
     (Matrix.of (fun i j : Fin L => lambda j ^ (p+i.val))) using 1 <;> rfl
 rw [hfactor]
 have hv : 0 < (Matrix.of (fun i j : Fin L => lambda j ^ (p+i.val))).det := by
   rw [← Matrix.det_transpose]
   convert generalizedMonomialVandermonde_det_pos L (fun i : Fin L => p+i.val)
     lambda (by intro i j hij; exact Nat.add_lt_add_left hij p) hl hp using 1 <;> rfl
 exact mul_pos (Finset.prod_pos (fun i _ => hw i)) hv

def weightedGeneralizedConfluent (p L : ℕ) (k : Fin L → ℕ)
 (lambda : Fin L → ℝ) (w : ℕ → ℝ) :
 Matrix (Fin p ⊕ Fin L) (Fin p ⊕ Fin L) ℝ :=
 Matrix.fromBlocks 1 (Matrix.of (fun i j => w i.val * lambda j ^ i.val)) 0
   (Matrix.of (fun i j => w (k i) * lambda j ^ k i))

theorem weightedGeneralizedConfluent_det_pos (p L : ℕ) (k : Fin L → ℕ)
 (lambda : Fin L → ℝ) (w : ℕ → ℝ) (hk : StrictMono k)
 (hl : StrictMono lambda) (hp : ∀ j, 0 < lambda j)
 (hw : ∀ i, 0 < w (k i)) :
 0 < (weightedGeneralizedConfluent p L k lambda w).det := by
 unfold weightedGeneralizedConfluent
 rw [Matrix.det_fromBlocks_zero₂₁,Matrix.det_one,one_mul]
 have hfactor : (Matrix.of (fun i j : Fin L => w (k i) * lambda j ^ k i)).det =
     (∏ i : Fin L, w (k i)) *
       (Matrix.of (fun i j : Fin L => lambda j ^ k i)).det := by
   convert Matrix.det_mul_column (fun i : Fin L => w (k i))
     (Matrix.of (fun i j : Fin L => lambda j ^ k i)) using 1 <;> rfl
 rw [hfactor]
 have hv : 0 < (Matrix.of (fun i j : Fin L => lambda j ^ k i)).det := by
   rw [← Matrix.det_transpose]
   convert generalizedMonomialVandermonde_det_pos L k lambda hk hl hp using 1 <;> rfl
 exact mul_pos (Finset.prod_pos (fun i _ => hw i)) hv

end
end JinWishart
#print axioms JinWishart.zeroConfluentVandermonde_det_pos
#print axioms JinWishart.weightedZeroConfluentVandermonde_det_pos
#print axioms JinWishart.weightedGeneralizedConfluent_det_pos
