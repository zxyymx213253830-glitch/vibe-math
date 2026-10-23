import JinWishartFormalization.LocalMGFLawUniqueness
import Lean
open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology
namespace SheafLocalMGF
def Target : Prop := ∀ {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {X : Ω → ℝ} {Y : Ω' → ℝ},
    AEMeasurable X μ → AEMeasurable Y ν →
    0 ∈ interior (integrableExpSet X μ) →
    0 ∈ interior (integrableExpSet Y ν) →
    mgf X μ =ᶠ[𝓝 0] mgf Y ν → μ.map X = ν.map Y
end SheafLocalMGF
open Lean Meta in
#eval show MetaM Unit from do
 let actualType ← inferType (← mkConstWithFreshMVarLevels `JinWishart.map_eq_of_mgf_eventuallyEq_zero)
 let expectedType ← whnf (← mkConstWithFreshMVarLevels `SheafLocalMGF.Target)
 unless ← isDefEq actualType expectedType do
  throwError "SHEAF local MGF target differs"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
