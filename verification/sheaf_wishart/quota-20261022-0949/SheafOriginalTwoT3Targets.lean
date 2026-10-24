import JinWishartFormalization.OriginalCentralTwoByTwoT3
import Lean
open JinWishart
namespace SheafOriginalTwoT3
noncomputable section
def Closed : Prop := ∀ x : ℝ,0≤x →
 theorem3IncrementCandidate 2 2 0 2 (by omega) (by omega) emptyNoncentralSpectrum x=
 (((x^2+2)*Real.exp (-x)-2*Real.exp (-2*x) : ℝ) : ℂ)
def Actual : Prop := ∀ x : ℝ,0≤x →
 theorem3IncrementCandidate 2 2 0 2 (by omega) (by omega) emptyNoncentralSpectrum x=
 ((centralTwoByTwoT3Increment x).toReal : ℂ)
def Recurrence : Prop := ∀ x : ℝ,0≤x →
 theorem1CdfCandidate 2 2 0 (by omega) (by omega) emptyNoncentralSpectrum.values x=
 theorem2CdfCandidate 2 2 0 (by omega) (by omega) emptyNoncentralSpectrum.values x+
 (theorem3IncrementCandidate 2 2 0 2 (by omega) (by omega) emptyNoncentralSpectrum x).re
end
end SheafOriginalTwoT3
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.theorem3CentralTwoSquare_candidate_eq_closed,`SheafOriginalTwoT3.Closed),
 (`JinWishart.theorem3CentralTwoSquare_candidate_eq_actual_crossing,`SheafOriginalTwoT3.Actual),
 (`JinWishart.theorem3CentralTwoSquare_original_recurrence,`SheafOriginalTwoT3.Recurrence)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Original two T3 literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
