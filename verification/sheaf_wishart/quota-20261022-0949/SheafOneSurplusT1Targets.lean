import JinWishartFormalization.Theorem1CentralOneSurplus
import Lean
open Matrix JinWishart MeasureTheory ProbabilityTheory
namespace SheafOneSurplusT1
noncomputable section
def PencilTarget : Prop := ∀ (n : ℕ) (x : ℂ),
 Matrix.det (fun i j : Fin n => ((i.val+j.val+1).factorial : ℂ)+x*((i.val+j.val).factorial : ℂ))=
 (∏ i : Fin n,(i.val.factorial : ℂ)*((i.val+1).factorial : ℂ))*
 ∑ k ∈ Finset.range (n+1),(n.choose k : ℂ)*x^k/(k.factorial : ℂ)
def GammaTarget : Prop := ∀ (n : ℕ) (x : ℝ),0≤x →
 Matrix.det (fun i j : Fin n => upperGammaNat (i.val+j.val+1) x)=
 (Real.exp (-(n : ℝ)*x) : ℂ)*(∏ i : Fin n,(i.val.factorial : ℂ)*((i.val+1).factorial : ℂ))*
 (oneExtraRowMinimumPolynomial n x : ℂ)
def PsiTarget : Prop := ∀ (n : ℕ) (x : ℝ),0≤x →
 (theorem1PsiMatrix n (n+1) 0 (by omega) (Nat.zero_le n) (fun j : Fin 0 => Fin.elim0 j) x).det=
 (Real.exp (-(n : ℝ)*x) : ℂ)*(∏ i : Fin n,(i.val.factorial : ℂ)*((i.val+1).factorial : ℂ))*
 (oneExtraRowMinimumPolynomial n x : ℂ)
def CandidateTarget : Prop := ∀ (n : ℕ) (x : ℝ),0≤x →
 theorem1CdfCandidate n (n+1) 0 (by omega) (Nat.zero_le n) (fun j : Fin 0 => Fin.elim0 j) x=
 1-Real.exp (-(n : ℝ)*x)*oneExtraRowMinimumPolynomial n x
def ActualTarget : Prop := ∀ (n : ℕ) (hn : 0<n) (x : ℝ),0≤x →
 theorem1CdfCandidate n (n+1) 0 (by omega) (Nat.zero_le n) (fun j : Fin 0 => Fin.elim0 j) x=
 ((stdGaussian (ComplexSample (m := n+1) (n := n))) {z | oneExtraRowSampleMinimum n hn z≤x}).toReal
end
end SheafOneSurplusT1
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
  (`JinWishart.factorialHankel_one_surplus_pencil_det,`SheafOneSurplusT1.PencilTarget),
  (`JinWishart.upperGammaHankel_one_surplus_det,`SheafOneSurplusT1.GammaTarget),
  (`JinWishart.theorem1CentralOneSurplus_PsiDet,`SheafOneSurplusT1.PsiTarget),
  (`JinWishart.theorem1CentralOneSurplus_candidate_eq_polynomial,`SheafOneSurplusT1.CandidateTarget),
  (`JinWishart.theorem1CentralOneSurplus_candidate_eq_actualCDF,`SheafOneSurplusT1.ActualTarget)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels name)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF one-surplus T1 target differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
