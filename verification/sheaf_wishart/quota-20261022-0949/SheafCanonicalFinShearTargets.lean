import JinWishartFormalization.CanonicalFinShear
import Lean
open Matrix JinWishart
namespace SheafCanonicalFinShear
noncomputable section
def InverseTarget : Prop := ∀ {b c n : ℕ} (e : (Fin b ⊕ Fin c) ≃ Fin n)
    (K : Matrix (Fin c) (Fin b) ℂ),
    canonicalFinShear e (-K)*canonicalFinShear e K=1 ∧
    canonicalFinShear e K*canonicalFinShear e (-K)=1 ∧
    (canonicalFinShear e (-K))⁻¹=canonicalFinShear e K
def NormTarget : Prop := ∀ {b c n : ℕ} (e : (Fin b ⊕ Fin c) ≃ Fin n)
    (K : Matrix (Fin c) (Fin b) ℂ),
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (canonicalFinShear e K)‖ ≤
      1+‖(Matrix.toEuclideanLin K).toContinuousLinearMap‖ ∧
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (canonicalFinShear e (-K))‖ ≤
      1+‖(Matrix.toEuclideanLin K).toContinuousLinearMap‖
def ControlTarget : Prop := ∀ {b c n : ℕ} (e : (Fin b ⊕ Fin c) ≃ Fin n)
    (K : Matrix (Fin c) (Fin b) ℂ),
    matrixColumnControl (canonicalFinShear e (-K)) ≤
      (1+‖(Matrix.toEuclideanLin K).toContinuousLinearMap‖)^2 ∧
    matrixColumnControl ((canonicalFinShear e (-K))⁻¹) ≤
      (1+‖(Matrix.toEuclideanLin K).toContinuousLinearMap‖)^2
end
end SheafCanonicalFinShear
open Lean Meta in
#eval show MetaM Unit from do
 for (target,expected) in [
 (`JinWishart.canonical_fin_shear_inverse,`SheafCanonicalFinShear.InverseTarget),
 (`JinWishart.canonical_fin_shear_opNorm_le,`SheafCanonicalFinShear.NormTarget),
 (`JinWishart.canonical_fin_shear_control_le,`SheafCanonicalFinShear.ControlTarget) ] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels target)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels expected)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF Fin shear target differs: {target}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
