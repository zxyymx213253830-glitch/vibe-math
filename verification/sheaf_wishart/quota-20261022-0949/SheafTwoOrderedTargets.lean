import JinWishartFormalization.TwoByTwoOrderedEigenpair
import Lean
open MeasureTheory ProbabilityTheory Set JinWishart
namespace SheafTwoOrdered
noncomputable section
def HermitianTarget : Prop := ∀ (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.IsHermitian),
 hA.eigenvalues₀ 0=((A 0 0).re+(A 1 1).re)/2+twoRowTracelessRadius A ∧
 hA.eigenvalues₀ 1=((A 0 0).re+(A 1 1).re)/2-twoRowTracelessRadius A
def ActualTarget : Prop := ∀ (z : ComplexSample (m := 2) (n := 2)),
 centralTwoByTwoEigenpair z=twoRowTraceSpectralPair
 (twoRowTraceCoordinates (twoRowGramRealCoordinates (complexGram (complexSampleMatrix z))))
end
end SheafTwoOrdered
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
  (`JinWishart.hermitian_twoRow_ordered_eigenpair,`SheafTwoOrdered.HermitianTarget),
  (`JinWishart.centralTwoByTwoEigenpair_eq_traceSpectralPair,`SheafTwoOrdered.ActualTarget)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels name)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq actualType expectedType do throwError "two-ordered literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
