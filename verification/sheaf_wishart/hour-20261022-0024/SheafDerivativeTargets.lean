import JinWishartFormalization.ExpectedLogDetDerivative
import Lean
open Matrix MeasureTheory ProbabilityTheory Filter
namespace SheafDerivative
noncomputable section
def Generic : Prop := ∀ {α : Type} [MeasurableSpace α] (μ : Measure α) (f : α→ℝ),
 Measurable f → Integrable f μ → (∀ᵐ a ∂μ,0≤f a) → ∀ r : ℝ,0<r →
 Integrable (fun a => f a/(1+r*f a)) μ ∧
 HasDerivAt (fun x : ℝ => ∫ a,Real.log (1+x*f a) ∂μ) (∫ a,f a/(1+r*f a) ∂μ) r
def Actual : Prop := ∀ {m p n : ℕ} (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ),
 ∀ r : ℝ,0<r → HasDerivAt (fun x : ℝ => ∫ z,JinWishart.actualCorrelatedMatrixLogDet B M x z ∂stdGaussian _)
 (∑ i,∫ z,JinWishart.actualCorrelatedEigenvalue B M i z/(1+r*JinWishart.actualCorrelatedEigenvalue B M i z) ∂stdGaussian _) r
end
end SheafDerivative
open Lean Meta in
#eval show MetaM Unit from do
 for (target,expected) in [
  (`JinWishart.integral_log_one_add_mul_hasDerivAt,`SheafDerivative.Generic),
  (`JinWishart.actualCorrelated_expected_logdet_hasDerivAt,`SheafDerivative.Actual)] do
   let actualType ← inferType (← mkConstWithFreshMVarLevels target)
   let expectedType ← whnf (← mkConstWithFreshMVarLevels expected)
   unless ← isDefEq actualType expectedType do
    throwError "SHEAF target type differs: {target}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
