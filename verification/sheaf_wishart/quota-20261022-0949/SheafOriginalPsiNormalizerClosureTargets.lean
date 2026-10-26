import JinWishartFormalization.NoncentralGammaMomentColumns
import JinWishartFormalization.ZeroConfluentVandermonde
import JinWishartFormalization.OriginalPsiNormalizerNonzero
import Lean
open Matrix Polynomial JinWishart
namespace SheafOriginalPsiNormalizerClosure
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
def MixedGammaSum : Prop := ∀ (q k p : ℕ) (h : Fin p),
 (∑ j : Fin p, (noncentralMomentPolynomial q k).coeff j.val *
   gammaMomentColumnTransform q p j h) = ((q+k+h.val).factorial : ℝ)
def MixedBasisDet : Prop := ∀ (q p L : ℕ), (mixedMomentCoefficientBasis q p L).det = 1
def MixedFactorization : Prop := ∀ (q p L : ℕ) (lambda : Fin L → ℝ),
 mixedNoncentralMomentMatrix q p L lambda =
   mixedMomentCoefficientBasis q p L * zeroConfluentVandermonde p L lambda *
     mixedGammaColumnBlock q p L
def MixedDeterminant : Prop := ∀ (q p L : ℕ) (lambda : Fin L → ℝ),
 (mixedNoncentralMomentMatrix q p L lambda).det =
   ((∏ j : Fin L, lambda j ^ p)*(Matrix.vandermonde lambda).det)*
     (∏ h : Fin p, (h.val.factorial : ℝ)*((q+h.val).factorial : ℝ))
def MixedNonzero : Prop := ∀ (q p L : ℕ) (lambda : Fin L → ℝ),
 (∀ j, lambda j ≠ 0) → Function.Injective lambda →
 (mixedNoncentralMomentMatrix q p L lambda).det ≠ 0
def OriginalNonzero : Prop := ∀ (s t L : ℕ) (hst : s ≤ t) (hLs : L ≤ s)
 (lambda : Fin L → ℝ), (∀ j, 0 < lambda j) → Function.Injective lambda →
 (theorem1PsiMatrix s t L hst hLs lambda 0).det ≠ 0
end
end SheafOriginalPsiNormalizerClosure
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.noncentralMomentPolynomial_eval,`SheafOriginalPsiNormalizerClosure.Eval),
 (`JinWishart.noncentralMomentPolynomial_monic,`SheafOriginalPsiNormalizerClosure.Monic),
 (`JinWishart.noncentralMomentPolynomial_natDegree,`SheafOriginalPsiNormalizerClosure.Degree),
 (`JinWishart.noncentralMoment_eval_det,`SheafOriginalPsiNormalizerClosure.EvalDet),
 (`JinWishart.theorem1PsiMatrix_zero_det_ne_zero_full_rank,`SheafOriginalPsiNormalizerClosure.Nonzero),
 (`JinWishart.noncentralMomentPolynomial_coeff,`SheafOriginalPsiNormalizerClosure.Coeff),
 (`JinWishart.noncentralMomentPolynomial_weighted_coeff,`SheafOriginalPsiNormalizerClosure.WeightedCoeff),
 (`JinWishart.gammaMoment_column_eq_coefficient_sum,`SheafOriginalPsiNormalizerClosure.GammaColumn),
 (`JinWishart.gammaMomentColumnTransform_det,`SheafOriginalPsiNormalizerClosure.TransformDet),
 (`JinWishart.gammaMomentColumnTransform_det_ne_zero,`SheafOriginalPsiNormalizerClosure.TransformNonzero),
 (`JinWishart.zeroConfluentVandermonde_det,`SheafOriginalPsiNormalizerClosure.ConfluentDet),
 (`JinWishart.zeroConfluentVandermonde_det_ne_zero,`SheafOriginalPsiNormalizerClosure.ConfluentNonzero),
 (`JinWishart.zeroConfluentVandermonde_eq_zero_of_conditions,`SheafOriginalPsiNormalizerClosure.Conditions),
 (`JinWishart.gammaMomentColumnTransform_coeff_sum,`SheafOriginalPsiNormalizerClosure.MixedGammaSum),
 (`JinWishart.mixedMomentCoefficientBasis_det,`SheafOriginalPsiNormalizerClosure.MixedBasisDet),
 (`JinWishart.mixedNoncentralMomentMatrix_factorization,`SheafOriginalPsiNormalizerClosure.MixedFactorization),
 (`JinWishart.mixedNoncentralMomentMatrix_det,`SheafOriginalPsiNormalizerClosure.MixedDeterminant),
 (`JinWishart.mixedNoncentralMomentMatrix_det_ne_zero,`SheafOriginalPsiNormalizerClosure.MixedNonzero),
 (`JinWishart.theorem1PsiMatrix_zero_det_ne_zero,`SheafOriginalPsiNormalizerClosure.OriginalNonzero)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Noncentral full rank normalizer literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
