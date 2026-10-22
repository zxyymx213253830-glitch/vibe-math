import JinWishartFormalization.CanonicalShearNorm
import Lean
open Matrix
namespace SheafCanonicalShearNorm
noncomputable section
def Plus : Prop := ∀ {b c : ℕ} (K : Matrix (Fin c) (Fin b) ℂ),
 ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (fromBlocks 1 0 K 1)‖ ≤
 1+‖(Matrix.toEuclideanLin K).toContinuousLinearMap‖
def Minus : Prop := ∀ {b c : ℕ} (K : Matrix (Fin c) (Fin b) ℂ),
 ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (fromBlocks 1 0 (-K) 1)‖ ≤
 1+‖(Matrix.toEuclideanLin K).toContinuousLinearMap‖
end
end SheafCanonicalShearNorm
open Lean Meta in
#eval show MetaM Unit from do
 for (target,expected) in [
 (`JinWishart.canonical_shear_opNorm_le,`SheafCanonicalShearNorm.Plus),
 (`JinWishart.canonical_inverse_shear_opNorm_le,`SheafCanonicalShearNorm.Minus)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels target)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels expected)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF target type differs: {target}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
