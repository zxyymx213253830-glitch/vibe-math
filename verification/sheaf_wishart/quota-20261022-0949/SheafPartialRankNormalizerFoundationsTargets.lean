import JinWishartFormalization.NoncentralGammaMomentColumns
import JinWishartFormalization.ZeroConfluentVandermonde
import Lean
open Matrix Polynomial JinWishart
namespace SheafPartialRankNormalizerFoundations
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
def ConfluentDet : Prop := ∀ (p L : ℕ) (lambda : Fin L → ℝ),
 (zeroConfluentVandermonde p L lambda).det =
   (∏ j : Fin L, lambda j ^ p)*(Matrix.vandermonde lambda).det
def ConfluentNonzero : Prop := ∀ (p L : ℕ) (lambda : Fin L → ℝ),
 (∀ j, lambda j ≠ 0) → Function.Injective lambda →
 (zeroConfluentVandermonde p L lambda).det ≠ 0
def Conditions : Prop := ∀ (p L : ℕ) (lambda : Fin L → ℝ),
 (∀ j, lambda j ≠ 0) → Function.Injective lambda →
 ∀ c : Fin p ⊕ Fin L → ℝ, (∀ i, c (Sum.inl i) = 0) →
 (∀ j : Fin L,
   (∑ i : Fin p, c (Sum.inl i)*lambda j^i.val)+
     (∑ i : Fin L, c (Sum.inr i)*lambda j^(p+i.val)) = 0) → c = 0
end
end SheafPartialRankNormalizerFoundations
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.noncentralMomentPolynomial_eval,`SheafPartialRankNormalizerFoundations.Eval),
 (`JinWishart.noncentralMomentPolynomial_monic,`SheafPartialRankNormalizerFoundations.Monic),
 (`JinWishart.noncentralMomentPolynomial_natDegree,`SheafPartialRankNormalizerFoundations.Degree),
 (`JinWishart.noncentralMoment_eval_det,`SheafPartialRankNormalizerFoundations.EvalDet),
 (`JinWishart.theorem1PsiMatrix_zero_det_ne_zero_full_rank,`SheafPartialRankNormalizerFoundations.Nonzero),
 (`JinWishart.noncentralMomentPolynomial_coeff,`SheafPartialRankNormalizerFoundations.Coeff),
 (`JinWishart.noncentralMomentPolynomial_weighted_coeff,`SheafPartialRankNormalizerFoundations.WeightedCoeff),
 (`JinWishart.gammaMoment_column_eq_coefficient_sum,`SheafPartialRankNormalizerFoundations.GammaColumn),
 (`JinWishart.gammaMomentColumnTransform_det,`SheafPartialRankNormalizerFoundations.TransformDet),
 (`JinWishart.gammaMomentColumnTransform_det_ne_zero,`SheafPartialRankNormalizerFoundations.TransformNonzero),
 (`JinWishart.zeroConfluentVandermonde_det,`SheafPartialRankNormalizerFoundations.ConfluentDet),
 (`JinWishart.zeroConfluentVandermonde_det_ne_zero,`SheafPartialRankNormalizerFoundations.ConfluentNonzero),
 (`JinWishart.zeroConfluentVandermonde_eq_zero_of_conditions,`SheafPartialRankNormalizerFoundations.Conditions)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Noncentral full rank normalizer literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
