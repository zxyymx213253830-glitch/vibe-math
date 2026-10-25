import JinWishartFormalization.CentralTwoColumnT3Normalization
import Lean
open MeasureTheory ProbabilityTheory JinWishart
namespace SheafTwoColumnT3Normalization
noncomputable section
def Raw : Prop := ∀ (d : ℕ) (x : ℝ), 0≤x →
 theorem3IncrementCandidate 2 (d+2) 0 2 (by omega) (by omega) emptyNoncentralSpectrum x =
 (((centralTwoColumnT3Factor d)*(centralTwoColumnStrictCrossing d x).toReal : ℝ) : ℂ)
def Derived : Prop := ∀ (d : ℕ) (x : ℝ), 0≤x →
 (theorem3DerivedC3 2 (d+2) 0 (by omega) emptyNoncentralSpectrum : ℂ)*
 theorem3ThetaDetSum 2 (d+2) 0 2 (by omega) (by omega) emptyNoncentralSpectrum x =
 ((centralTwoColumnStrictCrossing d x).toReal : ℂ)
end
end SheafTwoColumnT3Normalization
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.centralTwoColumn_originalT3_factor,`SheafTwoColumnT3Normalization.Raw),
 (`JinWishart.centralTwoColumn_derivedT3_probability,`SheafTwoColumnT3Normalization.Derived)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "T3 normalization literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
