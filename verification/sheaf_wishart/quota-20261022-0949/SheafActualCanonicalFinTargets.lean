import JinWishartFormalization.ActualCanonicalFinBridge
import Lean
open Matrix JinWishart MeasureTheory ProbabilityTheory
open scoped ComplexOrder
namespace SheafActualCanonicalFin
noncomputable section
def GramTarget : Prop := ∀ {m p n b a c : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (T : Matrix (Fin n) (Fin b ⊕ Fin c) ℂ) (U : Matrix (Fin p) (Fin b) ℂ)
    (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin a ⊕ Fin c))
    (A : Matrix (Fin a) (Fin b) ℂ) (H : Matrix (Fin c) (Fin b) ℂ)
    (N : Matrix (Fin c) (Fin c) ℂ)
    (er : (Fin a ⊕ Fin c) ≃ Fin m) (ec : (Fin b ⊕ Fin c) ≃ Fin n)
    (hBT : B*T=fromCols U 0)
    (hMean : (fromBlocks A 0 H N).toEuclideanLin=
      V.toLinearEquiv.toLinearMap.comp (M*T).toEuclideanLin)
    (Z : Matrix (Fin m) (Fin p) ℂ),
    let D := canonicalPhysicalFinSample er ec V U A H N Z
    Dᴴ*D=((Z*B+M)*(T.submatrix id ec.symm))ᴴ*((Z*B+M)*(T.submatrix id ec.symm))
def BoundsTarget : Prop := ∀ {m p n b a c : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (T : Matrix (Fin n) (Fin b ⊕ Fin c) ℂ) (U : Matrix (Fin p) (Fin b) ℂ)
    (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin a ⊕ Fin c))
    (A : Matrix (Fin a) (Fin b) ℂ) (H : Matrix (Fin c) (Fin b) ℂ)
    (N : Matrix (Fin c) (Fin c) ℂ)
    (er : (Fin a ⊕ Fin c) ≃ Fin m) (ec : (Fin b ⊕ Fin c) ≃ Fin n)
    (hBT : B*T=fromCols U 0)
    (hMean : (fromBlocks A 0 H N).toEuclideanLin=
      V.toLinearEquiv.toLinearMap.comp (M*T).toEuclideanLin)
    (hT : Function.Bijective T.toEuclideanLin) (hstack : (Matrix.fromRows B M).rank=n)
    (hm : 0<m) (hn : 0<n) (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=min m n),
    ∀ᵐ z ∂stdGaussian (ComplexSample (m := m) (n := p)),
      let D := canonicalPhysicalFinSample er ec V U A H N (complexSampleMatrix z)
      let F := T.submatrix id ec.symm
      0<actualCorrelatedEigenvalue B M i z ∧
      0<(complexGram_posSemidef D).1.eigenvalues₀ i ∧
      (complexGram_posSemidef D).1.eigenvalues₀ i≤
        max (matrixColumnControl F) (matrixColumnControl Fᴴ)*actualCorrelatedEigenvalue B M i z ∧
      actualCorrelatedEigenvalue B M i z≤
        max (matrixColumnControl F⁻¹) (matrixColumnControl (Fᴴ)⁻¹)*
          (complexGram_posSemidef D).1.eigenvalues₀ i
end
end SheafActualCanonicalFin
open Lean Meta in
#eval show MetaM Unit from do
 for (target,expected) in [
 (`JinWishart.canonical_physical_fin_gram,`SheafActualCanonicalFin.GramTarget),
 (`JinWishart.actual_canonical_fin_positive_bounds_ae,`SheafActualCanonicalFin.BoundsTarget) ] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels target)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels expected)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF actual canonical Fin target differs: {target}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
