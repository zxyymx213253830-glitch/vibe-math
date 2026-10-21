import Lean
import JinWishartFormalization.BivariateGaussianPolynomialLog

open MeasureTheory ProbabilityTheory
namespace SheafBivariateLog
noncomputable section
universe u

def ExpectedSection : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (P : α → Polynomial ℂ),
    Measurable (fun w : α × ℂ => (P w.1).eval w.2) →
    Integrable (fun a => max 0 (-Real.log ‖(P a).leadingCoeff‖)) μ →
    ∀ D : ℕ, (∀ᵐ a ∂μ, (P a).natDegree ≤ D) →
    Integrable (fun w : α × ℂ => max 0 (-Real.log ‖(P w.1).eval w.2‖))
      (μ.prod (stdGaussian ℂ)) ∧
    (∫ w : α × ℂ, max 0 (-Real.log ‖(P w.1).eval w.2‖) ∂μ.prod (stdGaussian ℂ)) ≤
      (∫ a, max 0 (-Real.log ‖(P a).leadingCoeff‖) ∂μ)+(D : ℝ)/4

def ExpectedZero : Prop := ∀ (P : Polynomial ℂ), P≠0 → ∀ᵐ z ∂stdGaussian ℂ, P.eval z≠0

def ExpectedSum : Prop := ∀ (P : Polynomial (Polynomial ℂ)) (w : ℂ × ℂ),
  (P.map (Polynomial.evalRingHom w.1)).eval w.2 = ∑ k ∈ P.support, (P.coeff k).eval w.1*w.2^k

def ExpectedContinuous : Prop := ∀ P : Polynomial (Polynomial ℂ),
  Continuous (fun w : ℂ × ℂ => (P.map (Polynomial.evalRingHom w.1)).eval w.2)

def ExpectedNegative : Prop := ∀ P : Polynomial (Polynomial ℂ),
  Integrable (fun w : ℂ × ℂ => max 0 (-Real.log ‖(P.map (Polynomial.evalRingHom w.1)).eval w.2‖))
    ((stdGaussian ℂ).prod (stdGaussian ℂ)) ∧
  (∫ w : ℂ × ℂ, max 0 (-Real.log ‖(P.map (Polynomial.evalRingHom w.1)).eval w.2‖)
    ∂(stdGaussian ℂ).prod (stdGaussian ℂ)) ≤
    max 0 (-Real.log ‖P.leadingCoeff.leadingCoeff‖)+
      (P.leadingCoeff.natDegree : ℝ)/4+(P.natDegree : ℝ)/4

def ExpectedEval : Prop := ∀ P : Polynomial (Polynomial ℂ),
  Integrable (fun w : ℂ × ℂ => (P.map (Polynomial.evalRingHom w.1)).eval w.2)
    ((stdGaussian ℂ).prod (stdGaussian ℂ))

def ExpectedLog : Prop := ∀ P : Polynomial (Polynomial ℂ),
  Integrable (fun w : ℂ × ℂ => Real.log ‖(P.map (Polynomial.evalRingHom w.1)).eval w.2‖)
    ((stdGaussian ℂ).prod (stdGaussian ℂ))

end
end SheafBivariateLog

open Lean Meta in
#eval show MetaM Unit from do
  for (target, expected) in [
      (`JinWishart.integrable_polynomial_section_negativeLog, `SheafBivariateLog.ExpectedSection),
      (`JinWishart.stdGaussian_complex_polynomial_eval_ne_zero_ae, `SheafBivariateLog.ExpectedZero),
      (`JinWishart.complexBivariateEval_eq_sum, `SheafBivariateLog.ExpectedSum),
      (`JinWishart.continuous_complexBivariateEval, `SheafBivariateLog.ExpectedContinuous),
      (`JinWishart.stdGaussian_bivariate_polynomial_negativeLog, `SheafBivariateLog.ExpectedNegative),
      (`JinWishart.integrable_stdGaussian_bivariate_polynomial_eval, `SheafBivariateLog.ExpectedEval),
      (`JinWishart.stdGaussian_bivariate_polynomial_log_integrable, `SheafBivariateLog.ExpectedLog)] do
    let actualType ← inferType (← mkConstWithFreshMVarLevels target)
    let expectedType ← whnf (← mkConstWithFreshMVarLevels expected)
    unless ← isDefEq actualType expectedType do
      throwError "SHEAF target type differs: {target}"
  IO.println "SHEAF_TARGET_TYPES_EQ PASS"

#print axioms JinWishart.integrable_polynomial_section_negativeLog
#print axioms JinWishart.stdGaussian_complex_polynomial_eval_ne_zero_ae
#print axioms JinWishart.complexBivariateEval_eq_sum
#print axioms JinWishart.continuous_complexBivariateEval
#print axioms JinWishart.stdGaussian_bivariate_polynomial_negativeLog
#print axioms JinWishart.integrable_stdGaussian_bivariate_polynomial_eval
#print axioms JinWishart.stdGaussian_bivariate_polynomial_log_integrable
