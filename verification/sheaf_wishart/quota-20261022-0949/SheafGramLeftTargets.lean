import JinWishartFormalization.GramMinimumLeftComparison
import Lean
open Matrix
namespace SheafGramLeft
noncomputable section
def Composition : Prop := ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
 (T : Matrix (Fin m) (Fin m) ℂ) (u : EuclideanSpace ℂ (Fin n)),
 (T*A).toEuclideanLin u =
 Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℂ) T (A.toEuclideanLin u)
def Upper : Prop := ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
 (T : Matrix (Fin m) (Fin m) ℂ) (hn : 0<n),
 JinWishart.gramSmallestValue (T*A) hn ≤
 JinWishart.matrixColumnControl T*JinWishart.gramSmallestValue A hn
def Lower : Prop := ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
 (T : Matrix (Fin m) (Fin m) ℂ) (hn : 0<n), IsUnit T.det →
 JinWishart.gramSmallestValue A hn ≤
 JinWishart.matrixColumnControl T⁻¹*JinWishart.gramSmallestValue (T*A) hn
end
end SheafGramLeft
open Lean Meta in
#eval show MetaM Unit from do
 for (target,expected) in [
 (`JinWishart.matrixLeft_composition,`SheafGramLeft.Composition),
 (`JinWishart.gramSmallestValue_mul_left_upper,`SheafGramLeft.Upper),
 (`JinWishart.gramSmallestValue_mul_left_lower,`SheafGramLeft.Lower)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels target)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels expected)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF target type differs: {target}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
