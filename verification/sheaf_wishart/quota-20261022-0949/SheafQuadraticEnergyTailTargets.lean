import JinWishartFormalization.QuadraticEnergyTailChange
import Lean
open MeasureTheory Set JinWishart
namespace SheafQuadraticEnergyTail
noncomputable section
def Image : Prop := ∀ a : ℝ, 0 ≤ a → (fun r : ℝ => r^2/2) '' Ioi a = Ioi (a^2/2)
def Integral : Prop := ∀ a : ℝ, 0 ≤ a → ∀ g : ℝ → ℝ,
 (∫ y in Ioi (a^2/2), g y) = ∫ r in Ioi a, r * g (r^2/2)
end
end SheafQuadraticEnergyTail
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.quadraticEnergy_image_Ioi,`SheafQuadraticEnergyTail.Image),
 (`JinWishart.quadraticEnergy_tail_substitution,`SheafQuadraticEnergyTail.Integral)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Quadratic energy tail literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
