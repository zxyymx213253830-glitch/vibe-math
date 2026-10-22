import JinWishartFormalization.FullRankPositiveCoordinateTransport
import Lean
open Matrix
open scoped ComplexOrder
namespace SheafPositiveTransport
noncomputable section
def ColumnTarget : Prop := ∀ {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (T : Matrix (Fin n) (Fin n) ℂ)
    (hn : 0<n) (hT : IsUnit T.det) (hr : A.rank=n)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=n),
    0<(complexGram_posSemidef A).1.eigenvalues₀ i ∧
    0<(complexGram_posSemidef (A*T)).1.eigenvalues₀ i ∧
    (complexGram_posSemidef (A*T)).1.eigenvalues₀ i ≤
      matrixColumnControl T*(complexGram_posSemidef A).1.eigenvalues₀ i ∧
    (complexGram_posSemidef A).1.eigenvalues₀ i ≤
      matrixColumnControl T⁻¹*(complexGram_posSemidef (A*T)).1.eigenvalues₀ i
def RowTarget : Prop := ∀ {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (T : Matrix (Fin n) (Fin n) ℂ)
    (hm : 0<m) (hT : IsUnit T.det) (hr : A.rank=m)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=m),
    0<(complexGram_posSemidef A).1.eigenvalues₀ i ∧
    0<(complexGram_posSemidef (A*T)).1.eigenvalues₀ i ∧
    (complexGram_posSemidef (A*T)).1.eigenvalues₀ i ≤
      matrixColumnControl Tᴴ*(complexGram_posSemidef A).1.eigenvalues₀ i ∧
    (complexGram_posSemidef A).1.eigenvalues₀ i ≤
      matrixColumnControl (Tᴴ)⁻¹*(complexGram_posSemidef (A*T)).1.eigenvalues₀ i
end
end SheafPositiveTransport
open Lean Meta in
#eval show MetaM Unit from do
 for (target,expected) in [
 (`JinWishart.full_column_rank_positive_coordinate_mul_bounds,`SheafPositiveTransport.ColumnTarget),
 (`JinWishart.full_row_rank_positive_coordinate_mul_bounds,`SheafPositiveTransport.RowTarget) ] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels target)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels expected)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF positive-coordinate transport type differs: {target}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
