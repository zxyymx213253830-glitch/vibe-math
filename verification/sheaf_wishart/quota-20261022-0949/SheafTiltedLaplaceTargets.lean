import JinWishartFormalization.DominatedLocalLaplaceUniqueness
import Lean
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace SheafTiltedLaplace
noncomputable section

def Dual : Prop := ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
 [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
 {μ ν : Measure E} [IsFiniteMeasure μ] [IsFiniteMeasure ν],
 (∀ L : E →L[ℝ] ℝ, 0 ∈ interior (integrableExpSet L μ)) →
 (∀ L : E →L[ℝ] ℝ, 0 ∈ interior (integrableExpSet L ν)) →
 (∀ L : E →L[ℝ] ℝ, mgf L μ =ᶠ[𝓝 0] mgf L ν) → μ = ν

def Tilt : Prop := ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
 [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
 {μ ν : Measure E} [IsFiniteMeasure μ] [IsFiniteMeasure ν] {f : E → ℝ},
 Measurable f → (∀ᵐ x ∂μ, ‖x‖ ≤ f x) → (∀ᵐ x ∂ν, ‖x‖ ≤ f x) →
 (∀ L : E →L[ℝ] ℝ, ‖L‖ < 1 →
  (∫ x, Real.exp (-f x + L x) ∂μ) = ∫ x, Real.exp (-f x + L x) ∂ν) → μ = ν
end
end SheafTiltedLaplace
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.eq_of_localMGF_all_dual,`SheafTiltedLaplace.Dual),
 (`JinWishart.eq_of_norm_dominated_localLaplace,`SheafTiltedLaplace.Tilt)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Generic tilted Laplace literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
