import JinWishartFormalization.PsiCandidateTailRatio
import Lean
open MeasureTheory Matrix Set JinWishart
namespace SheafPsiCandidateTailRatio
noncomputable section
def Reindex : Prop := ∀ {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
 (er ec : a ≃ b) (A : Matrix b b ℂ), ‖(A.submatrix er ec).det‖ = ‖A.det‖
def Restricted : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ) (x : ℝ), 0 ≤ x →
 (mixedCandidateTailMatrix p L q lambda x).det =
 (Matrix.of (fun i j => ∫ y in Ioi x,
   mixedEnsembleF p L i y * mixedEnsembleG p L q lambda j y
   ∂(volume.restrict (Ioi (0 : ℝ))))).det
def PsiNorm : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ), (∀ j, 0 ≤ lambda j) →
 ∀ x : ℝ, 0 ≤ x →
 ‖(theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda x).det‖ =
 (∏ j : Fin p ⊕ Fin L, psiTailColumnFactor p L q lambda j) *
   |(mixedCandidateTailMatrix p L q lambda x).det|
def Zero : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ),
 (mixedCandidateTailMatrix p L q lambda 0).det =
 (determinantMomentMatrix (volume.restrict (Ioi (0 : ℝ))) (mixedEnsembleF p L)
   (mixedEnsembleG p L q lambda)).det
def Nonnegative : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ), StrictMono lambda →
 (∀ j, 0 < lambda j) → ∀ x : ℝ, 0 ≤ x → 0 ≤ (mixedCandidateTailMatrix p L q lambda x).det
def Ratio : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ), StrictMono lambda →
 (∀ j, 0 < lambda j) → ∀ x : ℝ, 0 ≤ x →
 ((mixedCandidateEnsemble p L q lambda) {z | ∀ i, x < z i}).toReal =
 ‖(theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda x).det‖ /
 ‖(theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda 0).det‖
end
end SheafPsiCandidateTailRatio
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.norm_det_submatrix_equiv_equiv_complex,`SheafPsiCandidateTailRatio.Reindex),
 (`JinWishart.mixedCandidateTailMatrix_det_eq_restricted,`SheafPsiCandidateTailRatio.Restricted),
 (`JinWishart.paperPsi_tail_det_norm,`SheafPsiCandidateTailRatio.PsiNorm),
 (`JinWishart.mixedCandidateTailMatrix_zero_det,`SheafPsiCandidateTailRatio.Zero),
 (`JinWishart.mixedCandidateTailMatrix_det_nonneg,`SheafPsiCandidateTailRatio.Nonnegative),
 (`JinWishart.mixedCandidateEnsemble_all_gt_eq_paperPsi_ratio,`SheafPsiCandidateTailRatio.Ratio)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Psi candidate tail ratio literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
