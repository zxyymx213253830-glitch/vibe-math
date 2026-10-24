import JinWishartFormalization.ActualCentralTwoColumnMaximum
import Lean
open MeasureTheory ProbabilityTheory JinWishart Matrix
namespace SheafTwoColumnMaximum
noncomputable section
def Finite : Prop := ∀ (d : ℕ) (x : ℝ),IsFiniteMeasure (powerExponentialIntervalMeasure d x)
def Int : Prop := ∀ (d : ℕ) (x : ℝ) (k : ℕ),Integrable (fun y : ℝ => y^k) (powerExponentialIntervalMeasure d x)
def Gamma : Prop := ∀ (d : ℕ) (x : ℝ),0≤x → ∀ k : ℕ,
 ((∫ y : ℝ,y^k ∂powerExponentialIntervalMeasure d x : ℝ) : ℂ)=Complex.partialGamma ((d+k+1 : ℕ) : ℂ) x
def Xi : Prop := ∀ (d : ℕ) (x : ℝ),0≤x →
 (theorem2XiMatrix 2 (d+2) 0 (by omega) (by omega) (fun j : Fin 0 => Fin.elim0 j) x).det=
 (twoMomentDeterminant (powerExponentialIntervalMeasure d x) : ℂ)
def Moment : Prop := ∀ (d : ℕ) (x : ℝ),
 ((stdGaussian (ComplexSample (m := d+2) (n := 2))) {z | (centralTwoColumnEigenpair z).1≤x}).toReal=
 twoMomentDeterminant (powerExponentialIntervalMeasure d x)/((d.factorial : ℝ)*((d+1).factorial : ℝ))
def Den : Prop := ∀ d : ℕ,
 (theorem1PsiMatrix 2 (d+2) 0 (by omega) (by omega) (fun j : Fin 0 => Fin.elim0 j) 0).det=
 (((d.factorial : ℝ)*((d+1).factorial : ℝ) : ℝ) : ℂ)
def Original : Prop := ∀ (d : ℕ) (x : ℝ),0≤x →
 theorem2CdfCandidate 2 (d+2) 0 (by omega) (by omega) (fun j : Fin 0 => Fin.elim0 j) x=
 ((stdGaussian (ComplexSample (m := d+2) (n := 2))) {z | (centralTwoColumnEigenpair z).1≤x}).toReal
end
end SheafTwoColumnMaximum
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.powerExponentialIntervalMeasure_isFinite,`SheafTwoColumnMaximum.Finite),
 (`JinWishart.powerExponentialInterval_integrable_pow,`SheafTwoColumnMaximum.Int),
 (`JinWishart.powerExponentialInterval_integral_pow_eq_partialGamma,`SheafTwoColumnMaximum.Gamma),
 (`JinWishart.theorem2CentralTwoColumn_XiDet_eq_intervalMoments,`SheafTwoColumnMaximum.Xi),
 (`JinWishart.actualCentralTwoColumn_maximum_momentDet,`SheafTwoColumnMaximum.Moment),
 (`JinWishart.theorem1CentralTwoColumn_PsiDet_zero,`SheafTwoColumnMaximum.Den),
 (`JinWishart.theorem2CentralTwoColumn_candidate_eq_actualCDF,`SheafTwoColumnMaximum.Original)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Two column maximum literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
