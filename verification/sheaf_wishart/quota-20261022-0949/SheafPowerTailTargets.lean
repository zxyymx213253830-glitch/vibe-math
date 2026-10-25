import JinWishartFormalization.PowerExponentialTailMoments
import Lean
open MeasureTheory Matrix JinWishart
namespace SheafPowerTail
noncomputable section
def Finite : Prop := ∀ (d : ℕ) (x : ℝ),IsFiniteMeasure (powerExponentialTailMeasure d x)
def Int : Prop := ∀ (d : ℕ) (x : ℝ) (k : ℕ),Integrable (fun y : ℝ => y^k) (powerExponentialTailMeasure d x)
def Gamma : Prop := ∀ (d : ℕ) (x : ℝ),0≤x → ∀ k : ℕ,
 ((∫ y : ℝ,y^k ∂powerExponentialTailMeasure d x : ℝ) : ℂ)=upperGammaNat (d+k) x
def Psi : Prop := ∀ (d : ℕ) (x : ℝ),0≤x →
 (theorem1PsiMatrix 2 (d+2) 0 (by omega) (by omega) (fun j : Fin 0 => Fin.elim0 j) x).det=
 (twoMomentDeterminant (powerExponentialTailMeasure d x) : ℂ)
end
end SheafPowerTail
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.powerExponentialTailMeasure_isFinite,`SheafPowerTail.Finite),
 (`JinWishart.powerExponentialTail_integrable_pow,`SheafPowerTail.Int),
 (`JinWishart.powerExponentialTail_integral_pow_eq_upperGamma,`SheafPowerTail.Gamma),
 (`JinWishart.theorem1CentralTwoColumn_PsiDet_eq_tailMoments,`SheafPowerTail.Psi)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Power tail literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
