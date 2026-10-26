import JinWishartFormalization.NoncentralGammaMomentColumns
import Lean
open Matrix Polynomial JinWishart
namespace SheafFullRankGamma
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
def Coeff : Prop := ∀ (q k j : ℕ),
 (noncentralMomentPolynomial q k).coeff j =
   (k.factorial : ℝ)*((q+k).choose (q+j) : ℝ)/(j.factorial : ℝ)
def WeightedCoeff : Prop := ∀ (q k j : ℕ),
 ((q+j).factorial : ℝ)*(noncentralMomentPolynomial q k).coeff j =
   ((q+k).factorial : ℝ)*(k.choose j : ℝ)
def GammaColumn : Prop := ∀ (q k h : ℕ),
 (∑ j ∈ Finset.range (h+1), (h.factorial : ℝ)*((q+h).choose (h-j) : ℝ)*
   ((q+j).factorial : ℝ)*(noncentralMomentPolynomial q k).coeff j) =
     ((q+k+h).factorial : ℝ)
def TransformDet : Prop := ∀ (q p : ℕ),
 (gammaMomentColumnTransform q p).det =
   ∏ h : Fin p, (h.val.factorial : ℝ)*((q+h.val).factorial : ℝ)
def TransformNonzero : Prop := ∀ (q p : ℕ),
 (gammaMomentColumnTransform q p).det ≠ 0
end
end SheafFullRankGamma
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.noncentralMomentPolynomial_eval,`SheafFullRankGamma.Eval),
 (`JinWishart.noncentralMomentPolynomial_monic,`SheafFullRankGamma.Monic),
 (`JinWishart.noncentralMomentPolynomial_natDegree,`SheafFullRankGamma.Degree),
 (`JinWishart.noncentralMoment_eval_det,`SheafFullRankGamma.EvalDet),
 (`JinWishart.theorem1PsiMatrix_zero_det_ne_zero_full_rank,`SheafFullRankGamma.Nonzero),
 (`JinWishart.noncentralMomentPolynomial_coeff,`SheafFullRankGamma.Coeff),
 (`JinWishart.noncentralMomentPolynomial_weighted_coeff,`SheafFullRankGamma.WeightedCoeff),
 (`JinWishart.gammaMoment_column_eq_coefficient_sum,`SheafFullRankGamma.GammaColumn),
 (`JinWishart.gammaMomentColumnTransform_det,`SheafFullRankGamma.TransformDet),
 (`JinWishart.gammaMomentColumnTransform_det_ne_zero,`SheafFullRankGamma.TransformNonzero)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Noncentral full rank normalizer literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
