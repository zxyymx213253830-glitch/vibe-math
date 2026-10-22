import JinWishartFormalization.SeparableInverseMomentTransport
import Lean
open JinWishart MeasureTheory
namespace SheafSeparableInverse
noncomputable section
def TransportTarget : Prop := ∀ {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : α × β → ℝ) (g : α → ℝ) (K : β → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hK : ∀ y,0<K y)
    (p : ℝ) (hp : 0<p) (hKI : Integrable (fun y => (K y)^p) ν)
    (hb : ∀ᵐ z ∂μ.prod ν,0<f z ∧ 0<g z.1 ∧
      g z.1≤K z.2*f z ∧ f z≤K z.2*g z.1),
    Integrable (fun z => (f z)⁻¹^p) (μ.prod ν) ↔
      Integrable (fun x => (g x)⁻¹^p) μ
end
end SheafSeparableInverse
open Lean Meta in
#eval show MetaM Unit from do
 let actualType ← inferType (← mkConstWithFreshMVarLevels `JinWishart.integrable_inverse_rpow_iff_of_separable_comparison)
 let expectedType ← whnf (← mkConstWithFreshMVarLevels `SheafSeparableInverse.TransportTarget)
 unless ← isDefEq actualType expectedType do
  throwError "SHEAF separable inverse transport target differs"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
