import JinWishartFormalization.TwoSurplusGammaWronskian
import Lean
open Polynomial Matrix JinWishart
namespace SheafTwoSurplusGamma
noncomputable section
def Pencil : Prop := ∀ (n : ℕ) (x : ℂ),
 Matrix.det (fun i j : Fin n => ((i.val+j.val+2).factorial : ℂ)+2*x*((i.val+j.val+1).factorial : ℂ)+x^2*((i.val+j.val).factorial : ℂ)) =
 (∏ i : Fin n,(i.val.factorial : ℂ)^2)*twoSurplusLaguerreWronskian n x
def Gamma : Prop := ∀ (n : ℕ) (x : ℝ),0≤x →
 Matrix.det (fun i j : Fin n => upperGammaNat (i.val+j.val+2) x) =
 (Real.exp (-(n : ℝ)*x) : ℂ)*(∏ i : Fin n,(i.val.factorial : ℂ)^2)*twoSurplusLaguerreWronskian n (x : ℂ)
def Psi : Prop := ∀ (n : ℕ) (x : ℝ),0≤x →
 (theorem1PsiMatrix n (n+2) 0 (by omega) (Nat.zero_le n) (fun j : Fin 0 => Fin.elim0 j) x).det =
 (Real.exp (-(n : ℝ)*x) : ℂ)*(∏ i : Fin n,(i.val.factorial : ℂ)^2)*twoSurplusLaguerreWronskian n (x : ℂ)
end
end SheafTwoSurplusGamma
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.factorialHankel_two_surplus_pencil_det,`SheafTwoSurplusGamma.Pencil),
 (`JinWishart.upperGammaHankel_two_surplus_wronskian,`SheafTwoSurplusGamma.Gamma),
 (`JinWishart.theorem1CentralTwoSurplus_PsiDet_wronskian,`SheafTwoSurplusGamma.Psi)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Two surplus Gamma literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
