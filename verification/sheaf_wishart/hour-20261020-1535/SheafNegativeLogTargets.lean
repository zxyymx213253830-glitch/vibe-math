import Lean
import JinWishartFormalization.ProbabilityNegativeLogBounds
import JinWishartFormalization.ScalarUniformNegativeLog

open MeasureTheory Matrix ProbabilityTheory
namespace SheafNegativeLog
noncomputable section
universe u

def ExpectedTail : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → ℝ) (C : ℝ),
    (∀ x : ℝ, 0 < x → μ.real {a | f a ≤ x} ≤ C*x) →
    ∀ (t : ℝ), 0 < t →
      JinWishart.probabilityTail μ (fun a => max 0 (-Real.log (f a))) t ≤ C*Real.exp (-t)

def ExpectedMoment : Prop :=
  ∀ {α : Type u} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → ℝ), Measurable f → ∀ (C : ℝ), 0 ≤ C →
    (∀ x : ℝ, 0 < x → μ.real {a | f a ≤ x} ≤ C*x) →
    Integrable (fun a => max 0 (-Real.log (f a))) μ ∧
      (∫ a, max 0 (-Real.log (f a)) ∂μ) ≤ C

def ExpectedActual : Prop :=
  ∀ (M : Matrix (Fin 1) (Fin 1) ℂ),
    Integrable (fun z : JinWishart.ComplexSample (m := 1) (n := 1) =>
      max 0 (-Real.log (JinWishart.complexNoncentralSampleSmallestEigenvalue M (by norm_num) z)))
      (stdGaussian _) ∧
    (∫ z : JinWishart.ComplexSample (m := 1) (n := 1),
      max 0 (-Real.log (JinWishart.complexNoncentralSampleSmallestEigenvalue M (by norm_num) z))
      ∂(stdGaussian _)) ≤ 1

end
end SheafNegativeLog

open Lean Meta in
#eval show MetaM Unit from do
  for (target, expected) in [
      (`JinWishart.negativeLog_probabilityTail_le, `SheafNegativeLog.ExpectedTail),
      (`JinWishart.negativeLog_integrable_integral_le_of_smallball, `SheafNegativeLog.ExpectedMoment),
      (`JinWishart.actual_noncentralScalar_negativeLog_uniform_mean, `SheafNegativeLog.ExpectedActual)] do
    let actualType ← inferType (← mkConstWithFreshMVarLevels target)
    let expectedType ← whnf (← mkConstWithFreshMVarLevels expected)
    unless ← isDefEq actualType expectedType do
      throwError "SHEAF target type differs: {target}"
  IO.println "SHEAF_TARGET_TYPES_EQ PASS"

#print axioms JinWishart.negativeLog_probabilityTail_le
#print axioms JinWishart.negativeLog_integrable_integral_le_of_smallball
#print axioms JinWishart.actual_noncentralScalar_negativeLog_uniform_mean
