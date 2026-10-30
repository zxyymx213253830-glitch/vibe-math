import JinWishartFormalization.T3FixedCardinalityRowSelection
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! Codex. Seed 2026103105 exact small polynomial matrices precede source.
Generic affine determinant transport, no random-matrix law asserted.
[需人工审查] Later paper row/column orientation and model mapping. -/
open Matrix Finset Polynomial
namespace JinWishart
noncomputable section

theorem rowAffine_det_submatrix_complex {a b : Type*} [Fintype a] [Fintype b]
 [DecidableEq a] [DecidableEq b] (er ec : a ≃ b) (A B : Matrix b b ℂ) :
 (rowAffinePolynomialMatrix (A.submatrix er ec) (B.submatrix er ec)).det =
 ((Equiv.Perm.sign (ec.symm.trans er) : ℤˣ) : Polynomial ℂ) *
   (rowAffinePolynomialMatrix A B).det := by
 change ((rowAffinePolynomialMatrix A B).reindex er.symm ec.symm).det = _
 rw [Matrix.det_reindex]
 simp only [Equiv.symm_symm]

theorem rowAffine_det_columnScale_complex {a : Type*} [Fintype a] [DecidableEq a]
 (d : a → ℂ) (A B : Matrix a a ℂ) :
 (rowAffinePolynomialMatrix (Matrix.of (fun i j => d j*A i j))
   (Matrix.of (fun i j => d j*B i j))).det =
 Polynomial.C (∏ j, d j) * (rowAffinePolynomialMatrix A B).det := by
 have hm : rowAffinePolynomialMatrix (Matrix.of (fun i j => d j*A i j))
     (Matrix.of (fun i j => d j*B i j)) =
     Matrix.of (fun i j => Polynomial.C (d j) * rowAffinePolynomialMatrix A B i j) := by
   ext i j
   simp only [rowAffinePolynomialMatrix,Matrix.of_apply,map_mul]
   ring
 rw [hm,Matrix.det_mul_row]
 rw [← map_prod]

theorem rowAffine_det_realToComplex {a : Type*} [Fintype a] [DecidableEq a]
 (A B : Matrix a a ℝ) :
 (rowAffinePolynomialMatrix (Complex.ofRealHom.mapMatrix A) (Complex.ofRealHom.mapMatrix B)).det =
 ((rowAffinePolynomialMatrix A B).det).map Complex.ofRealHom := by
 let φ := Polynomial.mapRingHom Complex.ofRealHom
 have hm : rowAffinePolynomialMatrix (Complex.ofRealHom.mapMatrix A) (Complex.ofRealHom.mapMatrix B) =
     φ.mapMatrix (rowAffinePolynomialMatrix A B) := by
   ext i j
   simp [φ,rowAffinePolynomialMatrix]
 rw [hm,← φ.map_det]
 rfl

end
end JinWishart
#print axioms JinWishart.rowAffine_det_submatrix_complex
#print axioms JinWishart.rowAffine_det_columnScale_complex
#print axioms JinWishart.rowAffine_det_realToComplex
