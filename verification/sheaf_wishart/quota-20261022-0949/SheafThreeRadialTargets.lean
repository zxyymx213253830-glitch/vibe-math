import JinWishartFormalization.ThreeDimensionalRadialIntegral
import Lean
open MeasureTheory Set JinWishart
open scoped ENNReal
namespace SheafThreeRadial
def Target : Prop := ∀ (f : ℝ → ℝ≥0∞), Measurable f →
 (∫⁻ v : EuclideanSpace ℝ (Fin 3), f ‖v‖) =
 ENNReal.ofReal (4*Real.pi) * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r^2)*f r
end SheafThreeRadial
open Lean Meta in
#eval show MetaM Unit from do
 let actual ← inferType (mkConst `JinWishart.lintegral_norm_volume_fin_three)
 let target ← whnf (mkConst `SheafThreeRadial.Target)
 unless ← isDefEq actual target do throwError "three-radial literal type mismatch"
 logInfo "THREE_RADIAL_LITERAL_TYPE_PASS"
