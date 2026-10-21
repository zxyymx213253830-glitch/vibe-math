import JinWishartFormalization.FiniteComplexGaussianPolynomialLog
import Lean
open MeasureTheory ProbabilityTheory
namespace SheafFinitePi
noncomputable section

def ExpectedSplit : Prop := ∀ n : ℕ,
 MeasurePreserving (JinWishart.planarGaussianSplit n)
  (Measure.pi (fun _ : Fin (n+1) => stdGaussian ℂ))
  ((Measure.pi (fun _ : Fin n => stdGaussian ℂ)).prod (stdGaussian ℂ))
def ExpectedCons : Prop := ∀ (n : ℕ) (x : Fin (n+1) → ℂ),
 Fin.cons (JinWishart.planarGaussianSplit n x).2 (JinWishart.planarGaussianSplit n x).1=x
def ExpectedNull : Prop := ∀ (n : ℕ) (P : MvPolynomial (Fin n) ℂ), P≠0 →
 ∀ᵐ x ∂Measure.pi (fun _ : Fin n => stdGaussian ℂ), MvPolynomial.eval x P≠0
def ExpectedNegative : Prop := ∀ (n : ℕ) (P : MvPolynomial (Fin n) ℂ),
 Integrable (fun x => max 0 (-Real.log ‖MvPolynomial.eval x P‖))
  (Measure.pi (fun _ : Fin n => stdGaussian ℂ))
def ExpectedEval : Prop := ∀ (n : ℕ) (P : MvPolynomial (Fin n) ℂ),
 Integrable (fun x => MvPolynomial.eval x P) (Measure.pi (fun _ : Fin n => stdGaussian ℂ))
def ExpectedLog : Prop := ∀ (n : ℕ) (P : MvPolynomial (Fin n) ℂ),
 Integrable (fun x => Real.log ‖MvPolynomial.eval x P‖)
  (Measure.pi (fun _ : Fin n => stdGaussian ℂ))
end
end SheafFinitePi
open Lean Meta in
#eval show MetaM Unit from do
 for (target,expected) in [
  (`JinWishart.planarGaussianSplit_measurePreserving,`SheafFinitePi.ExpectedSplit),
  (`JinWishart.planarGaussianSplit_cons,`SheafFinitePi.ExpectedCons),
  (`JinWishart.stdGaussian_pi_mvPolynomial_ne_zero_ae,`SheafFinitePi.ExpectedNull),
  (`JinWishart.stdGaussian_pi_mvPolynomial_negativeLog_integrable,`SheafFinitePi.ExpectedNegative),
  (`JinWishart.integrable_stdGaussian_pi_mvPolynomial_eval,`SheafFinitePi.ExpectedEval),
  (`JinWishart.stdGaussian_pi_mvPolynomial_log_integrable,`SheafFinitePi.ExpectedLog)] do
   let actualType ← inferType (← mkConstWithFreshMVarLevels target)
   let expectedType ← whnf (← mkConstWithFreshMVarLevels expected)
   unless ← isDefEq actualType expectedType do
    throwError "SHEAF target type differs: {target}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
