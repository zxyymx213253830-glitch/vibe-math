import JinWishartFormalization.Theorem1ZeroMomentMatrix
import Lean
open Matrix MeasureTheory Set Finset JinWishart
namespace SheafNoncentralFullMoments
noncomputable section
def ChooseSum : Prop := ∀ (x : ℝ) (j : ℕ),
 HasSum (fun n : ℕ => x^n/(n.factorial : ℝ)*(n.choose j : ℝ))
   (x^j/(j.factorial : ℝ)*Real.exp x)
def FactorialRatio : Prop := ∀ (q k n : ℕ),
 ((n+q+k).factorial : ℝ)/((n+q).factorial : ℝ) =
   (k.factorial : ℝ)* ∑ j ∈ range (k+1),
     ((q+k).choose (k-j) : ℝ)*(n.choose j : ℝ)
def MomentSum : Prop := ∀ (q k : ℕ) (x : ℝ),
 HasSum (fun n : ℕ => (x^n/(n.factorial : ℝ))*
   (((n+q+k).factorial : ℝ)/((n+q).factorial : ℝ)))
   (Real.exp x*poissonFactorialMomentPolynomial q k x)
def RadialMoment : Prop := ∀ (q k : ℕ) (a : ℝ),
 (∫ r in Ioi (0 : ℝ), (r^2/2)^k*noncentralChiEvenRadialKernel q a r) =
   poissonFactorialMomentPolynomial q k (a^2/2)
def RadialL1 : Prop := ∀ (q k : ℕ) (a : ℝ),
 IntegrableOn (fun r : ℝ => (r^2/2)^k*noncentralChiEvenRadialKernel q a r) (Ioi 0)
def NuttallMoment : Prop := ∀ (q k : ℕ) (a : ℝ),
 nuttallQ (q+2*k+1) q a 0 = (a : ℂ)^q*(2 : ℂ)^k*
   (poissonFactorialMomentPolynomial q k (a^2/2) : ℂ)
def NuttallL1 : Prop := ∀ (q k : ℕ) (a : ℝ),
 IntegrableOn (nuttallQIntegrand (q+2*k+1) q a) (Ioi 0)
def PsiZero : Prop := ∀ (s t L : ℕ) (hst : s ≤ t) (hLs : L ≤ s)
 (lambda : Fin L → ℝ), (∀ j, 0 ≤ lambda j) →
 theorem1PsiMatrix s t L hst hLs lambda 0 = theorem1ZeroMomentMatrix s t L lambda
end
end SheafNoncentralFullMoments
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.poisson_choose_hasSum,`SheafNoncentralFullMoments.ChooseSum),
 (`JinWishart.factorial_ratio_vandermonde,`SheafNoncentralFullMoments.FactorialRatio),
 (`JinWishart.poisson_factorialMoment_hasSum,`SheafNoncentralFullMoments.MomentSum),
 (`JinWishart.noncentralChiEvenRadialKernel_energyMoment,`SheafNoncentralFullMoments.RadialMoment),
 (`JinWishart.integrableOn_noncentralChiEvenRadialKernel_energyMoment,`SheafNoncentralFullMoments.RadialL1),
 (`JinWishart.nuttallQ_fullNaturalMoment,`SheafNoncentralFullMoments.NuttallMoment),
 (`JinWishart.integrableOn_nuttallQ_fullNaturalMoment,`SheafNoncentralFullMoments.NuttallL1),
 (`JinWishart.theorem1PsiMatrix_at_zero_eq_finiteMoments,`SheafNoncentralFullMoments.PsiZero)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Noncentral full moment literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
