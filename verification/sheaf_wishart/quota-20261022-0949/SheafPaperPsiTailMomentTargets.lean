import JinWishartFormalization.PaperPsiTailMomentBridge
import Lean
open MeasureTheory Matrix Set JinWishart
namespace SheafPaperPsiTailMoment
noncomputable section
def Central : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ) (x : ℝ), 0 ≤ x →
 ∀ (i : Fin p ⊕ Fin L) (a : Fin p),
 mixedCandidateTailMatrix p L q lambda x i (Sum.inl a) =
 ∫ y in Ioi x, y^(q+mixedMomentDegree p L i+a.val)*Real.exp (-y)
def Noncentral : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ) (x : ℝ), 0 ≤ x →
 ∀ (i : Fin p ⊕ Fin L) (j : Fin L),
 mixedCandidateTailMatrix p L q lambda x i (Sum.inr j) =
 ∫ y in Ioi x, y^(q+mixedMomentDegree p L i)*Real.exp (-y)*scalarSeriesKernel q (lambda j) y
def Transport : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ), (∀ j, 0 ≤ lambda j) →
 ∀ x : ℝ, 0 ≤ x →
 (theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda x).submatrix
   (psiZeroRowEquiv p L) (psiZeroColumnEquiv p L) =
 Complex.ofRealHom.mapMatrix (Matrix.of (fun i j =>
   psiTailColumnFactor p L q lambda j * mixedCandidateTailMatrix p L q lambda x i j))
end
end SheafPaperPsiTailMoment
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.mixedCandidateTailMatrix_central,`SheafPaperPsiTailMoment.Central),
 (`JinWishart.mixedCandidateTailMatrix_noncentral,`SheafPaperPsiTailMoment.Noncentral),
 (`JinWishart.paperPsi_tail_matrix_transport,`SheafPaperPsiTailMoment.Transport)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Paper Psi tail matrix literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
