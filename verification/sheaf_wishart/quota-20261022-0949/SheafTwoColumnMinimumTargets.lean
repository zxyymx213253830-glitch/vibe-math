import JinWishartFormalization.ActualCentralTwoColumnMinimum
import Lean
open MeasureTheory ProbabilityTheory JinWishart
namespace SheafTwoColumnMinimum
noncomputable section
def Tail : Prop := ∀ (d : ℕ) (x : ℝ),0≤x →
 ((stdGaussian (ComplexSample (m := d+2) (n := 2))) {z | x<(centralTwoColumnEigenpair z).2}).toReal=
 twoMomentDeterminant (powerExponentialTailMeasure d x)/((d.factorial : ℝ)*((d+1).factorial : ℝ))
def Original : Prop := ∀ (d : ℕ) (x : ℝ),0≤x →
 theorem1CdfCandidate 2 (d+2) 0 (by omega) (by omega) (fun j : Fin 0 => Fin.elim0 j) x=
 ((stdGaussian (ComplexSample (m := d+2) (n := 2))) {z | (centralTwoColumnEigenpair z).2≤x}).toReal
end
end SheafTwoColumnMinimum
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.actualCentralTwoColumn_minimum_tail_momentDet,`SheafTwoColumnMinimum.Tail),
 (`JinWishart.theorem1CentralTwoColumn_candidate_eq_actualCDF,`SheafTwoColumnMinimum.Original)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Two column minimum literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
