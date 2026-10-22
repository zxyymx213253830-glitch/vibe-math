import JinWishartFormalization.CanonicalPhysicalModel
import Lean
open Matrix MeasureTheory ProbabilityTheory JinWishart
namespace SheafCanonicalPhysical
noncomputable section
def IdentityTarget : Prop := ∀ {m p n b a c : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (T : Matrix (Fin n) (Fin b ⊕ Fin c) ℂ) (U : Matrix (Fin p) (Fin b) ℂ)
    (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin a ⊕ Fin c))
    (A : Matrix (Fin a) (Fin b) ℂ) (H : Matrix (Fin c) (Fin b) ℂ)
    (N : Matrix (Fin c) (Fin c) ℂ)
    (hBT : B*T=fromCols U 0)
    (hMean : (fromBlocks A 0 H N).toEuclideanLin=
      V.toLinearEquiv.toLinearMap.comp (M*T).toEuclideanLin)
    (Z : Matrix (Fin m) (Fin p) ℂ),
    canonicalSumRowAction V ((Z*B+M)*T)=
      fromBlocks
        (fun i j => V (complexMatrixColumn (Z*U) j) (Sum.inl i)+A i j) 0
        (fun i j => V (complexMatrixColumn (Z*U) j) (Sum.inr i)+H i j) N
def LawTarget : Prop := ∀ {m p n b a c : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (T : Matrix (Fin n) (Fin b ⊕ Fin c) ℂ) (U : Matrix (Fin p) (Fin b) ℂ)
    (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin a ⊕ Fin c))
    (A : Matrix (Fin a) (Fin b) ℂ) (H : Matrix (Fin c) (Fin b) ℂ)
    (N : Matrix (Fin c) (Fin c) ℂ) (hU : Uᴴ*U=1)
    (hBT : B*T=fromCols U 0)
    (hMean : (fromBlocks A 0 H N).toEuclideanLin=
      V.toLinearEquiv.toLinearMap.comp (M*T).toEuclideanLin),
    (stdGaussian (ComplexSample (m := m) (n := p))).map (fun z =>
      ((canonicalSumRowAction V ((complexSampleMatrix z*B+M)*T)).toBlocks₁₁,
       (canonicalSumRowAction V ((complexSampleMatrix z*B+M)*T)).toBlocks₂₁))=
      (complexGaussianMatrixLaw A).prod (complexGaussianMatrixLaw H)
end
end SheafCanonicalPhysical
open Lean Meta in
#eval show MetaM Unit from do
 for (target,expected) in [
 (`JinWishart.canonical_physical_sample_block_identity,`SheafCanonicalPhysical.IdentityTarget),
 (`JinWishart.canonical_physical_sample_block_law,`SheafCanonicalPhysical.LawTarget) ] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels target)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels expected)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF canonical physical target differs: {target}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
