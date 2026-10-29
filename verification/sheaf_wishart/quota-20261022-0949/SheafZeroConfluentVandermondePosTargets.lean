import JinWishartFormalization.ZeroConfluentVandermondePos
import Lean
open Matrix JinWishart
namespace SheafZeroConfluentVandermondePos
noncomputable section
def Basic : Prop := ∀ (p L : ℕ) (lambda : Fin L → ℝ),
 StrictMono lambda → (∀ j, 0 < lambda j) →
 0 < (zeroConfluentVandermonde p L lambda).det
def Weighted : Prop := ∀ (p L : ℕ) (lambda : Fin L → ℝ) (w : ℕ → ℝ),
 StrictMono lambda → (∀ j, 0 < lambda j) → (∀ i : Fin L, 0 < w (p+i.val)) →
 0 < (weightedZeroConfluentVandermonde p L lambda w).det
def Generalized : Prop := ∀ (p L : ℕ) (k : Fin L → ℕ) (lambda : Fin L → ℝ)
 (w : ℕ → ℝ), StrictMono k → StrictMono lambda → (∀ j, 0 < lambda j) →
 (∀ i, 0 < w (k i)) → 0 < (weightedGeneralizedConfluent p L k lambda w).det
end
end SheafZeroConfluentVandermondePos
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
  (`JinWishart.zeroConfluentVandermonde_det_pos,`SheafZeroConfluentVandermondePos.Basic),
  (`JinWishart.weightedZeroConfluentVandermonde_det_pos,`SheafZeroConfluentVandermondePos.Weighted),
  (`JinWishart.weightedGeneralizedConfluent_det_pos,`SheafZeroConfluentVandermondePos.Generalized)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Confluent positivity literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
