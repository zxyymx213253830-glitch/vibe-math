import JinWishartFormalization.ProperGaussianAdjointLaw
import Lean
open Matrix MeasureTheory ProbabilityTheory
namespace SheafProperGaussianAdjoint
noncomputable section
def Scalar : Prop := JinWishart.standardComplexScalarLaw.map (star : ℂ→ℂ)=
 JinWishart.standardComplexScalarLaw
def Product : Prop := ∀ {ι : Type*} [Fintype ι],
 (JinWishart.standardComplexPiLaw ι).map (fun z i=>star (z i))=JinWishart.standardComplexPiLaw ι
def Conjugate : Prop := ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ),
 (JinWishart.complexGaussianMatrixLaw M).map (fun X=>X.map star)=
 JinWishart.complexGaussianMatrixLaw (M.map star)
def Adjoint : Prop := ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ),
 (JinWishart.complexGaussianMatrixLaw M).map Matrix.conjTranspose=
 JinWishart.complexGaussianMatrixLaw Mᴴ
end
end SheafProperGaussianAdjoint
open Lean Meta in
#eval show MetaM Unit from do
 for (target,expected) in [
 (`JinWishart.standardComplexScalarLaw_map_conj,`SheafProperGaussianAdjoint.Scalar),
 (`JinWishart.standardComplexPiLaw_map_conj,`SheafProperGaussianAdjoint.Product),
 (`JinWishart.complexGaussianMatrixLaw_conjugate,`SheafProperGaussianAdjoint.Conjugate),
 (`JinWishart.complexGaussianMatrixLaw_conjTranspose,`SheafProperGaussianAdjoint.Adjoint)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels target)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels expected)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF target type differs: {target}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
