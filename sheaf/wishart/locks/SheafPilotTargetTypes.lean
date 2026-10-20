import Lean
import JinWishartFormalization.ScalarUniformSmallBall

open Matrix MeasureTheory ProbabilityTheory

namespace SheafPilot
noncomputable section

def ExpectedPlanarBall : Prop :=
  ∀ (μ : ℂ) (R : ℝ), 0 ≤ R →
    (stdGaussian ℂ).real (Metric.closedBall μ R) ≤ R^2/2

def ExpectedActualCDF : Prop :=
  ∀ (M : Matrix (Fin 1) (Fin 1) ℂ) (x : ℝ), 0 ≤ x →
    cdf ((stdGaussian (JinWishart.ComplexSample (m := 1) (n := 1))).map
      (JinWishart.complexNoncentralSampleSmallestEigenvalue M (by norm_num))) x ≤ x

end
end SheafPilot

open Lean Meta in
#eval show MetaM Unit from do
  for (target, expected) in [
      (`JinWishart.stdGaussian_complex_closedBall_le_radius_sq_half, `SheafPilot.ExpectedPlanarBall),
      (`JinWishart.actual_noncentralScalarCDF_le_threshold_uniform_mean, `SheafPilot.ExpectedActualCDF)] do
    let actual ← getConstInfo target
    let expected ← getConstInfoDefn expected
    unless ← isDefEq actual.type expected.value do
      throwError "SHEAF target type differs: {target}"
  IO.println "SHEAF_TARGET_TYPES_EQ PASS"

#print axioms JinWishart.stdGaussian_complex_closedBall_le_radius_sq_half
#print axioms JinWishart.actual_noncentralScalarCDF_le_threshold_uniform_mean
