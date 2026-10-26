import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-! Codex. Seed2026102607 exact controls precede source.
Zero-confluent COEFFICIENT conditions, not derivative columns with factorials.
This is deterministic algebra, not a Wishart density or Psi-matrix identification.
[需人工审查] Fin/Sum index assembly in later use. -/
open Matrix Finset
namespace JinWishart
noncomputable section

def zeroConfluentVandermonde (p L : ℕ) (lambda : Fin L → ℝ) :
 Matrix (Fin p ⊕ Fin L) (Fin p ⊕ Fin L) ℝ :=
 Matrix.fromBlocks 1 (Matrix.of (fun i j => lambda j ^ i.val)) 0
   (Matrix.of (fun i j => lambda j ^ (p+i.val)))

theorem zeroConfluentVandermonde_det (p L : ℕ) (lambda : Fin L → ℝ) :
 (zeroConfluentVandermonde p L lambda).det =
   (∏ j : Fin L, lambda j ^ p)*(Matrix.vandermonde lambda).det := by
 unfold zeroConfluentVandermonde
 rw [Matrix.det_fromBlocks_zero₂₁,Matrix.det_one,one_mul]
 have he : Matrix.of (fun i j : Fin L => lambda j ^ (p+i.val)) =
   Matrix.of (fun i j => lambda j ^ p * (Matrix.vandermonde lambda).transpose i j) := by
   ext i j
   simp [Matrix.vandermonde,Matrix.transpose_apply,pow_add]
 rw [he,Matrix.det_mul_row,Matrix.det_transpose]

theorem zeroConfluentVandermonde_det_ne_zero (p L : ℕ) (lambda : Fin L → ℝ)
 (hnz : ∀ j, lambda j ≠ 0) (hinj : Function.Injective lambda) :
 (zeroConfluentVandermonde p L lambda).det ≠ 0 := by
 rw [zeroConfluentVandermonde_det]
 apply mul_ne_zero ?_ (Matrix.det_vandermonde_ne_zero_iff.mpr hinj)
 apply Finset.prod_ne_zero_iff.mpr
 intro j _
 exact pow_ne_zero p (hnz j)

theorem zeroConfluentVandermonde_eq_zero_of_conditions (p L : ℕ) (lambda : Fin L → ℝ)
 (hnz : ∀ j, lambda j ≠ 0) (hinj : Function.Injective lambda)
 (c : Fin p ⊕ Fin L → ℝ) (hc : ∀ i, c (Sum.inl i) = 0)
 (he : ∀ j : Fin L,
   (∑ i : Fin p, c (Sum.inl i)*lambda j^i.val)+
     (∑ i : Fin L, c (Sum.inr i)*lambda j^(p+i.val)) = 0) : c = 0 := by
 apply Matrix.eq_zero_of_vecMul_eq_zero
   (zeroConfluentVandermonde_det_ne_zero p L lambda hnz hinj)
 funext j
 cases j with
 | inl j =>
   simp [Matrix.vecMul,dotProduct,zeroConfluentVandermonde,Fintype.sum_sum_type,Matrix.fromBlocks,hc]
 | inr j =>
   simpa [Matrix.vecMul,dotProduct,zeroConfluentVandermonde,Fintype.sum_sum_type,Matrix.fromBlocks] using he j

end
end JinWishart
#print axioms JinWishart.zeroConfluentVandermonde_det
#print axioms JinWishart.zeroConfluentVandermonde_det_ne_zero
#print axioms JinWishart.zeroConfluentVandermonde_eq_zero_of_conditions
