import JinWishartFormalization.FourDimensionalRadialIntegral
import Lean
open MeasureTheory Set JinWishart
open scoped ENNReal
namespace SheafFourRadial
noncomputable section
def SplitTarget : Prop := MeasurePreserving traceVectorCoordinates
def IntegralTarget : Prop := ∀ (F : ℝ × ℝ → ℝ≥0∞),Measurable F →
 (∫⁻ p : GramChartSpace, F ((traceVectorCoordinates p).1,‖(traceVectorCoordinates p).2‖)) =
 ENNReal.ofReal (4*Real.pi) * ∫⁻ t : ℝ, ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r^2)*F (t,r)
end
end SheafFourRadial
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
  (`JinWishart.measurePreserving_traceVectorCoordinates,`SheafFourRadial.SplitTarget),
  (`JinWishart.lintegral_trace_radius_fin_four,`SheafFourRadial.IntegralTarget)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels name)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq actualType expectedType do throwError "four-radial literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
