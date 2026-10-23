import JinWishartFormalization.ActualCanonicalInverseTransport
import Lean
open Matrix JinWishart MeasureTheory ProbabilityTheory
namespace SheafActualCanonicalInverse
noncomputable section
def CriterionTarget : Prop := ∀ {m p n b a c : ℕ}
    (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (T : Matrix (Fin n) (Fin b ⊕ Fin c) ℂ) (U : Matrix (Fin p) (Fin b) ℂ)
    (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin a ⊕ Fin c))
    (MA : Matrix (Fin a) (Fin b) ℂ) (MH : Matrix (Fin c) (Fin b) ℂ)
    (N : Matrix (Fin c) (Fin c) ℂ)
    (er : (Fin a ⊕ Fin c) ≃ Fin m) (ec : (Fin b ⊕ Fin c) ≃ Fin n)
    (hBT : B*T=fromCols U 0) (hU : Uᴴ*U=1)
    (hMean : (fromBlocks MA 0 MH N).toEuclideanLin=
      V.toLinearEquiv.toLinearMap.comp (M*T).toEuclideanLin)
    (hT : Function.Bijective T.toEuclideanLin) (hN : IsUnit N.det)
    (hstack : (Matrix.fromRows B M).rank=n)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=min m n)
    (j : Fin (Fintype.card (Fin b))) (hj : j.val+1=min a b)
    (k : Fin (Fintype.card (Fin c))) (hk : k.val+1=c) (q : ℝ) (hq : 0<q),
    Integrable (fun z => (actualCorrelatedEigenvalue B M i z)⁻¹^q)
      (stdGaussian (ComplexSample (m := m) (n := p))) ↔
      q<((max a b-min a b+1 : ℕ) : ℝ)
end
end SheafActualCanonicalInverse
open Lean Meta in
#eval show MetaM Unit from do
 let actualType ← inferType (← mkConstWithFreshMVarLevels `JinWishart.actual_canonical_inverse_realMoment_integrable_iff)
 let expectedType ← whnf (← mkConstWithFreshMVarLevels `SheafActualCanonicalInverse.CriterionTarget)
 unless ← isDefEq actualType expectedType do
  throwError "SHEAF actual canonical inverse criterion target differs"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
