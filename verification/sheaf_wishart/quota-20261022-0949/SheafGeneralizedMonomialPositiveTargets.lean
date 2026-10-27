import JinWishartFormalization.GeneralizedMonomialVandermondePos
import Lean
open Matrix JinWishart
namespace SheafGeneralizedMonomialPositive
noncomputable section
def Positive : Prop := ∀ (n : ℕ) (k : Fin n → ℕ) (x : Fin n → ℝ),
 StrictMono k → StrictMono x → (∀ i, 0 < x i) →
 0 < (Matrix.of (fun i j : Fin n => x i ^ k j)).det
end
end SheafGeneralizedMonomialPositive
open Lean Meta in
#eval show MetaM Unit from do
 let a ← inferType (← mkConstWithFreshMVarLevels `JinWishart.generalizedMonomialVandermonde_det_pos)
 let e ← whnf (← mkConstWithFreshMVarLevels `SheafGeneralizedMonomialPositive.Positive)
 unless ← isDefEq a e do throwError "Generalized monomial positivity literal type differs"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
