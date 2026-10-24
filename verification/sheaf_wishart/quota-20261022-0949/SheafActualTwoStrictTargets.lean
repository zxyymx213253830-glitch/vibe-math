import JinWishartFormalization.ActualCentralTwoByTwoStrictCrossing
import Lean
open MeasureTheory ProbabilityTheory Set JinWishart
namespace SheafActualTwoStrict
noncomputable section
def Atoms : Prop := ∀ x : ℝ,
 (stdGaussian (ComplexSample (m := 2) (n := 2))) {z | (centralTwoByTwoEigenpair z).1=x}=0 ∧
 (stdGaussian (ComplexSample (m := 2) (n := 2))) {z | (centralTwoByTwoEigenpair z).2=x}=0
def Recurrence : Prop := ∀ x : ℝ,
 (stdGaussian (ComplexSample (m := 2) (n := 2))) {z | (centralTwoByTwoEigenpair z).2≤x}=
 (stdGaussian (ComplexSample (m := 2) (n := 2))) {z | (centralTwoByTwoEigenpair z).1≤x}+
 centralTwoByTwoT3Increment x
def Closed : Prop := ∀ x : ℝ,0≤x →
 (centralTwoByTwoT3Increment x).toReal=(x^2+2)*Real.exp (-x)-2*Real.exp (-2*x)
end
end SheafActualTwoStrict
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
  (`JinWishart.actualCentralTwoByTwo_coordinate_atoms_zero,`SheafActualTwoStrict.Atoms),
  (`JinWishart.actualCentralTwoByTwo_strict_CDF_recurrence,`SheafActualTwoStrict.Recurrence),
  (`JinWishart.actualCentralTwoByTwo_T3Increment_closed,`SheafActualTwoStrict.Closed)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Literal strict crossing type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
