import JinWishartFormalization.Theorem1CentralTwoSurplus
import Lean
open Polynomial Finset Matrix MeasureTheory ProbabilityTheory JinWishart
namespace SheafCentralTwoSurplus
noncomputable section
def Recurrence : Prop := ∀ n : ℕ,
 ((n+2 : ℕ) : ℂ) • positiveLaguerrePolynomial (n+2) =
 (X+C (2*(n : ℂ)+3))*positiveLaguerrePolynomial (n+1)-((n+1 : ℕ) : ℂ) • positiveLaguerrePolynomial n
def CD : Prop := ∀ (n : ℕ) (x : ℂ),((n+1 : ℕ) : ℂ)*
 ((positiveLaguerrePolynomial n).eval x*(Polynomial.derivative (positiveLaguerrePolynomial (n+1))).eval x-
 (positiveLaguerrePolynomial (n+1)).eval x*(Polynomial.derivative (positiveLaguerrePolynomial n)).eval x) =
 ∑ j ∈ range (n+1),((positiveLaguerrePolynomial j).eval x)^2
def Eval : Prop := ∀ (n : ℕ) (x : ℝ),
 (positiveLaguerrePolynomial n).eval (x : ℂ)=(oneExtraRowMinimumPolynomial n x : ℂ)
def Wronskian : Prop := ∀ (n : ℕ) (x : ℝ),twoSurplusLaguerreWronskian n (x : ℂ)=
 (((n.factorial : ℝ)*((n+1).factorial : ℝ)*twoExtraRowMinimumPolynomial n x : ℝ) : ℂ)
def Candidate : Prop := ∀ (n : ℕ) (x : ℝ),0≤x →
 theorem1CdfCandidate n (n+2) 0 (by omega) (Nat.zero_le n) (fun j : Fin 0 => Fin.elim0 j) x =
 1-Real.exp (-(n : ℝ)*x)*twoExtraRowMinimumPolynomial n x
def Actual : Prop := ∀ (n : ℕ) (hn : 0<n) (x : ℝ),0≤x →
 theorem1CdfCandidate n (n+2) 0 (by omega) (Nat.zero_le n) (fun j : Fin 0 => Fin.elim0 j) x =
 ((stdGaussian (ComplexSample (m := n+2) (n := n))) {z | centralGaussianSampleMinimum (n+2) n hn z≤x}).toReal
end
end SheafCentralTwoSurplus
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.positiveLaguerre_recurrence,`SheafCentralTwoSurplus.Recurrence),
 (`JinWishart.positiveLaguerre_christoffelDarboux,`SheafCentralTwoSurplus.CD),
 (`JinWishart.positiveLaguerre_eval_real,`SheafCentralTwoSurplus.Eval),
 (`JinWishart.twoSurplusLaguerreWronskian_eq_actualPolynomial,`SheafCentralTwoSurplus.Wronskian),
 (`JinWishart.theorem1CentralTwoSurplus_candidate_eq_polynomial,`SheafCentralTwoSurplus.Candidate),
 (`JinWishart.theorem1CentralTwoSurplus_candidate_eq_actualCDF,`SheafCentralTwoSurplus.Actual)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "All-size original T1 two surplus literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
