import JinWishartFormalization.ActualCanonicalNoiseBlockLaw
import Lean
open Matrix MeasureTheory ProbabilityTheory
namespace SheafCanonicalGaussian
noncomputable section
def AdjointTarget : Prop := ∀ {ι κ : Type*} [Fintype ι] [Fintype κ]
 (U : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ),
 (stdGaussian (EuclideanSpace ℂ κ)).map U.adjoint=stdGaussian (EuclideanSpace ℂ ι)
def ColumnTarget : Prop := ∀ {p b n : ℕ}
 (U : EuclideanSpace ℂ (Fin b) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin p)),
 (JinWishart.complexGaussianMatrixLaw (0 : Matrix (Fin p) (Fin n) ℂ)).map
 (fun A i j => U.adjoint (JinWishart.complexMatrixColumn A j) i)=
 JinWishart.complexGaussianMatrixLaw (0 : Matrix (Fin b) (Fin n) ℂ)
def RightTarget : Prop := ∀ {m p b : ℕ} (U : Matrix (Fin p) (Fin b) ℂ) (hU : Uᴴ*U=1),
 (JinWishart.complexGaussianMatrixLaw (0 : Matrix (Fin m) (Fin p) ℂ)).map
 (fun Z => Z*U)=JinWishart.complexGaussianMatrixLaw (0 : Matrix (Fin m) (Fin b) ℂ)
def DisjointColumnsTarget : Prop := ∀ {m n k l : ℕ}
 (M : Matrix (Fin m) (Fin n) ℂ) (e : Fin k → Fin n) (f : Fin l → Fin n)
 (h : Function.Injective (Sum.elim e f)),
 (JinWishart.complexGaussianMatrixLaw M).map (fun A => (A.submatrix id e,A.submatrix id f))=
 (JinWishart.complexGaussianMatrixLaw (M.submatrix id e)).prod
 (JinWishart.complexGaussianMatrixLaw (M.submatrix id f))
def DisjointRowsTarget : Prop := ∀ {m n a c : ℕ}
 (M : Matrix (Fin m) (Fin n) ℂ) (e : Fin a → Fin m) (f : Fin c → Fin m)
 (h : Function.Injective (Sum.elim e f)),
 (JinWishart.complexGaussianMatrixLaw M).map (fun A => (A.submatrix e id,A.submatrix f id))=
 (JinWishart.complexGaussianMatrixLaw (M.submatrix e id)).prod
 (JinWishart.complexGaussianMatrixLaw (M.submatrix f id))
def ActualTarget : Prop := ∀ {m p b a c : ℕ}
 (U : Matrix (Fin p) (Fin b) ℂ) (hU : Uᴴ*U=1)
 (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m))
 (M : Matrix (Fin m) (Fin b) ℂ) (e : Fin a → Fin m) (f : Fin c → Fin m)
 (h : Function.Injective (Sum.elim e f)),
 (stdGaussian (JinWishart.ComplexSample (m := m) (n := p))).map (fun z =>
 ((JinWishart.unitaryActColumns V (JinWishart.complexSampleMatrix z*U)+M).submatrix e id,
  (JinWishart.unitaryActColumns V (JinWishart.complexSampleMatrix z*U)+M).submatrix f id))=
 (JinWishart.complexGaussianMatrixLaw (M.submatrix e id)).prod
 (JinWishart.complexGaussianMatrixLaw (M.submatrix f id))
end
end SheafCanonicalGaussian
open Lean Meta in
#eval show MetaM Unit from do
 for (target,expected) in [
 (`JinWishart.stdGaussian_complex_isometry_adjoint_law,`SheafCanonicalGaussian.AdjointTarget),
 (`JinWishart.complexGaussianMatrixLaw_rectangular_column_projection,`SheafCanonicalGaussian.ColumnTarget),
 (`JinWishart.complexGaussianMatrixLaw_right_isometric_projection,`SheafCanonicalGaussian.RightTarget),
 (`JinWishart.complexGaussianMatrixLaw_disjoint_columns,`SheafCanonicalGaussian.DisjointColumnsTarget),
 (`JinWishart.complexGaussianMatrixLaw_disjoint_rows,`SheafCanonicalGaussian.DisjointRowsTarget),
 (`JinWishart.actual_isometric_noise_disjoint_row_blocks,`SheafCanonicalGaussian.ActualTarget)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels target)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels expected)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF canonical Gaussian type differs: {target}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
