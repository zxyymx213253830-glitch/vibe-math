import JinWishartFormalization.CanonicalFinGramTransport
import Lean
open Matrix JinWishart
open scoped ComplexOrder
namespace SheafCanonicalFin
noncomputable section
def GramTarget : Prop := ∀ {m a c : ℕ} {ι : Type*}
    (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin a ⊕ Fin c))
    (X : Matrix (Fin m) ι ℂ),
    (canonicalSumRowAction V X)ᴴ*(canonicalSumRowAction V X)=Xᴴ*X
def UnitTarget : Prop := ∀ {n b c : ℕ}
    (T : Matrix (Fin n) (Fin b ⊕ Fin c) ℂ)
    (hT : Function.Bijective T.toEuclideanLin) (e : (Fin b ⊕ Fin c) ≃ Fin n),
    IsUnit (T.submatrix id e.symm).det
def BoundsTarget : Prop := ∀ {m n b c a d : ℕ}
    (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin a ⊕ Fin d))
    (X : Matrix (Fin m) (Fin n) ℂ) (T : Matrix (Fin n) (Fin b ⊕ Fin c) ℂ)
    (hT : Function.Bijective T.toEuclideanLin) (e : (Fin b ⊕ Fin c) ≃ Fin n)
    (hm : 0<m) (hn : 0<n) (hr : X.rank=min m n)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=min m n),
    let F := T.submatrix id e.symm
    0<(complexGram_posSemidef X).1.eigenvalues₀ i ∧
    0<canonicalFiniteGramCoordinate V X T e i ∧
    canonicalFiniteGramCoordinate V X T e i ≤
      max (matrixColumnControl F) (matrixColumnControl Fᴴ)*
        (complexGram_posSemidef X).1.eigenvalues₀ i ∧
    (complexGram_posSemidef X).1.eigenvalues₀ i ≤
      max (matrixColumnControl F⁻¹) (matrixColumnControl (Fᴴ)⁻¹)*
        canonicalFiniteGramCoordinate V X T e i
end
end SheafCanonicalFin
open Lean Meta in
#eval show MetaM Unit from do
 for (target,expected) in [
 (`JinWishart.canonicalSumRowAction_gram,`SheafCanonicalFin.GramTarget),
 (`JinWishart.canonical_reindexed_column_det_isUnit,`SheafCanonicalFin.UnitTarget),
 (`JinWishart.canonical_fin_positive_coordinate_bounds,`SheafCanonicalFin.BoundsTarget) ] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels target)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels expected)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF canonical Fin target differs: {target}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
