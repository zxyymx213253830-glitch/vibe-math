import JinWishartFormalization.RowAffineDeterminantTransport
import Lean
open Matrix Finset Polynomial JinWishart
namespace SheafRowAffineTransport
def Reindex : Prop := ∀ {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
 (er ec : a ≃ b) (A B : Matrix b b ℂ),
 (rowAffinePolynomialMatrix (A.submatrix er ec) (B.submatrix er ec)).det =
 ((Equiv.Perm.sign (ec.symm.trans er) : ℤˣ) : Polynomial ℂ) *
   (rowAffinePolynomialMatrix A B).det
def Scale : Prop := ∀ {a : Type} [Fintype a] [DecidableEq a]
 (d : a → ℂ) (A B : Matrix a a ℂ),
 (rowAffinePolynomialMatrix (Matrix.of (fun i j => d j*A i j))
   (Matrix.of (fun i j => d j*B i j))).det =
 Polynomial.C (∏ j, d j) * (rowAffinePolynomialMatrix A B).det
def Map : Prop := ∀ {a : Type} [Fintype a] [DecidableEq a] (A B : Matrix a a ℝ),
 (rowAffinePolynomialMatrix (Complex.ofRealHom.mapMatrix A) (Complex.ofRealHom.mapMatrix B)).det =
 ((rowAffinePolynomialMatrix A B).det).map Complex.ofRealHom
end SheafRowAffineTransport
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.rowAffine_det_submatrix_complex,`SheafRowAffineTransport.Reindex),
 (`JinWishart.rowAffine_det_columnScale_complex,`SheafRowAffineTransport.Scale),
 (`JinWishart.rowAffine_det_realToComplex,`SheafRowAffineTransport.Map)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Row affine determinant transport literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
