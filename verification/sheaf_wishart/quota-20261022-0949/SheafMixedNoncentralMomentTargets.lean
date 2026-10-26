import JinWishartFormalization.MixedNoncentralMomentMatrix
import Lean
open Matrix Polynomial JinWishart
namespace SheafMixedNoncentralMoment
def GammaSum : Prop := ∀ (q k p : ℕ) (h : Fin p),
 (∑ j : Fin p, (noncentralMomentPolynomial q k).coeff j.val *
   gammaMomentColumnTransform q p j h) = ((q+k+h.val).factorial : ℝ)
def BasisDet : Prop := ∀ (q p L : ℕ), (mixedMomentCoefficientBasis q p L).det = 1
def Factorization : Prop := ∀ (q p L : ℕ) (lambda : Fin L → ℝ),
 mixedNoncentralMomentMatrix q p L lambda =
   mixedMomentCoefficientBasis q p L * zeroConfluentVandermonde p L lambda *
     mixedGammaColumnBlock q p L
def Determinant : Prop := ∀ (q p L : ℕ) (lambda : Fin L → ℝ),
 (mixedNoncentralMomentMatrix q p L lambda).det =
   ((∏ j : Fin L, lambda j ^ p)*(Matrix.vandermonde lambda).det)*
     (∏ h : Fin p, (h.val.factorial : ℝ)*((q+h.val).factorial : ℝ))
def Nonzero : Prop := ∀ (q p L : ℕ) (lambda : Fin L → ℝ),
 (∀ j, lambda j ≠ 0) → Function.Injective lambda →
 (mixedNoncentralMomentMatrix q p L lambda).det ≠ 0
end SheafMixedNoncentralMoment
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.gammaMomentColumnTransform_coeff_sum,`SheafMixedNoncentralMoment.GammaSum),
 (`JinWishart.mixedMomentCoefficientBasis_det,`SheafMixedNoncentralMoment.BasisDet),
 (`JinWishart.mixedNoncentralMomentMatrix_factorization,`SheafMixedNoncentralMoment.Factorization),
 (`JinWishart.mixedNoncentralMomentMatrix_det,`SheafMixedNoncentralMoment.Determinant),
 (`JinWishart.mixedNoncentralMomentMatrix_det_ne_zero,`SheafMixedNoncentralMoment.Nonzero)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Mixed noncentral moment literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
