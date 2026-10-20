import Lean
import JinWishartFormalization.ComplexGaussianRootNegativeLog
import JinWishartFormalization.ComplexGaussianPolynomialLog

open MeasureTheory ProbabilityTheory
namespace SheafPolynomialLog
noncomputable section

def ExpectedMul : Prop := ∀ a b : ℂ,
  max 0 (-Real.log ‖a*b‖) ≤ max 0 (-Real.log ‖a‖)+max 0 (-Real.log ‖b‖)

def ExpectedRoot : Prop := ∀ r : ℂ,
  Integrable (fun z : ℂ => max 0 (-Real.log ‖z-r‖)) (stdGaussian ℂ) ∧
    (∫ z : ℂ, max 0 (-Real.log ‖z-r‖) ∂stdGaussian ℂ) ≤ 1/4

def ExpectedProduct : Prop := ∀ l : List ℂ,
  Integrable (fun z : ℂ => max 0 (-Real.log ‖(l.map (fun r => z-r)).prod‖)) (stdGaussian ℂ) ∧
    (∫ z : ℂ, max 0 (-Real.log ‖(l.map (fun r => z-r)).prod‖) ∂stdGaussian ℂ)
      ≤ (l.length : ℝ)/4

def ExpectedPolynomialNegative : Prop := ∀ P : Polynomial ℂ,
  Integrable (fun z : ℂ => max 0 (-Real.log ‖P.eval z‖)) (stdGaussian ℂ) ∧
    (∫ z : ℂ, max 0 (-Real.log ‖P.eval z‖) ∂stdGaussian ℂ) ≤
      max 0 (-Real.log ‖P.leadingCoeff‖)+(P.natDegree : ℝ)/4

def ExpectedPolynomialEval : Prop := ∀ P : Polynomial ℂ,
  Integrable (fun z : ℂ => P.eval z) (stdGaussian ℂ)

def ExpectedPolynomialLog : Prop := ∀ P : Polynomial ℂ,
  Integrable (fun z : ℂ => Real.log ‖P.eval z‖) (stdGaussian ℂ)

end
end SheafPolynomialLog

open Lean Meta in
#eval show MetaM Unit from do
  for (target, expected) in [
      (`JinWishart.complexNegativeLog_mul_le, `SheafPolynomialLog.ExpectedMul),
      (`JinWishart.stdGaussian_complex_negativeLog_uniform_root, `SheafPolynomialLog.ExpectedRoot),
      (`JinWishart.stdGaussian_complex_rootProduct_negativeLog, `SheafPolynomialLog.ExpectedProduct),
      (`JinWishart.stdGaussian_complex_polynomial_negativeLog, `SheafPolynomialLog.ExpectedPolynomialNegative),
      (`JinWishart.integrable_stdGaussian_complex_polynomial_eval, `SheafPolynomialLog.ExpectedPolynomialEval),
      (`JinWishart.stdGaussian_complex_polynomial_log_integrable, `SheafPolynomialLog.ExpectedPolynomialLog)] do
    let actualType ← inferType (← mkConstWithFreshMVarLevels target)
    let expectedType ← whnf (← mkConstWithFreshMVarLevels expected)
    unless ← isDefEq actualType expectedType do
      throwError "SHEAF target type differs: {target}"
  IO.println "SHEAF_TARGET_TYPES_EQ PASS"

#print axioms JinWishart.complexNegativeLog_mul_le
#print axioms JinWishart.stdGaussian_complex_negativeLog_uniform_root
#print axioms JinWishart.stdGaussian_complex_rootProduct_negativeLog
#print axioms JinWishart.stdGaussian_complex_polynomial_negativeLog
#print axioms JinWishart.integrable_stdGaussian_complex_polynomial_eval
#print axioms JinWishart.stdGaussian_complex_polynomial_log_integrable
