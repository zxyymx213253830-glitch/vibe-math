import JinWishartFormalization.GammaTailMomentBridge
import Lean
open MeasureTheory Set JinWishart
namespace SheafGammaTailMoment
noncomputable section
def Tail : Prop := ∀ (k : ℕ) (x : ℝ), 0 ≤ x →
 upperGammaNat k x = ((∫ y in Ioi x, y^k*Real.exp (-y) : ℝ) : ℂ)
end
end SheafGammaTailMoment
open Lean Meta in
#eval show MetaM Unit from do
 let a ← inferType (← mkConstWithFreshMVarLevels `JinWishart.upperGammaNat_eq_realTailMoment)
 let e ← whnf (← mkConstWithFreshMVarLevels `SheafGammaTailMoment.Tail)
 unless ← isDefEq a e do throwError "Gamma tail literal type differs"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
