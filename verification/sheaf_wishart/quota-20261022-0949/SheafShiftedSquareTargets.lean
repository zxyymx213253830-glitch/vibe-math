import JinWishartFormalization.GaussianShiftedSquareMGF
import Lean
open MeasureTheory ProbabilityTheory
namespace SheafShiftedSquare
noncomputable section
def IntegralTarget : Prop := ∀ (u t : ℝ), t<1 →
    (∫ x : ℝ, Real.exp (t*(x+u)^2/2) ∂gaussianReal 0 1) =
      (Real.sqrt (1-t))⁻¹ * Real.exp (u^2*t/(2*(1-t)))
def IntegrableTarget : Prop := ∀ (u t : ℝ), t<1 →
    Integrable (fun x : ℝ => Real.exp (t*(x+u)^2/2)) (gaussianReal 0 1)
end
end SheafShiftedSquare
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
  (`JinWishart.gaussianReal_integral_exp_shifted_square,`SheafShiftedSquare.IntegralTarget),
  (`JinWishart.gaussianReal_integrable_exp_shifted_square,`SheafShiftedSquare.IntegrableTarget)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels name)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF shifted-square target differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
