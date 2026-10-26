import JinWishartFormalization.NoncentralFullRankNormalizer
import Lean
open Matrix Polynomial JinWishart
namespace SheafNoncentralFullRankNormalizer
noncomputable section
def Eval : Prop := ∀ (q k : ℕ) (x : ℝ),
 (noncentralMomentPolynomial q k).eval x = poissonFactorialMomentPolynomial q k x
def Monic : Prop := ∀ (q k : ℕ), (noncentralMomentPolynomial q k).Monic
def Degree : Prop := ∀ (q k : ℕ), (noncentralMomentPolynomial q k).natDegree = k
def EvalDet : Prop := ∀ (q s : ℕ) (lambda : Fin s → ℝ),
 (Matrix.of (fun i j : Fin s => poissonFactorialMomentPolynomial q i.val (lambda j))).det =
   (Matrix.vandermonde lambda).det
def Nonzero : Prop := ∀ (s t : ℕ) (hst : s ≤ t) (lambda : Fin s → ℝ),
 (∀ j, 0 < lambda j) → Function.Injective lambda →
 (theorem1PsiMatrix s t s hst le_rfl lambda 0).det ≠ 0
end
end SheafNoncentralFullRankNormalizer
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.noncentralMomentPolynomial_eval,`SheafNoncentralFullRankNormalizer.Eval),
 (`JinWishart.noncentralMomentPolynomial_monic,`SheafNoncentralFullRankNormalizer.Monic),
 (`JinWishart.noncentralMomentPolynomial_natDegree,`SheafNoncentralFullRankNormalizer.Degree),
 (`JinWishart.noncentralMoment_eval_det,`SheafNoncentralFullRankNormalizer.EvalDet),
 (`JinWishart.theorem1PsiMatrix_zero_det_ne_zero_full_rank,`SheafNoncentralFullRankNormalizer.Nonzero)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Noncentral full rank normalizer literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
