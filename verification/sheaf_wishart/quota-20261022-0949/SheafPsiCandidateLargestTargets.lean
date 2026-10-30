import JinWishartFormalization.PsiCandidateLargestCDF
import Lean
open MeasureTheory Matrix Set JinWishart
namespace SheafPsiCandidateLargest
noncomputable section
def LowerDet : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ), (∀ j, 0 ≤ lambda j) →
 ∀ x : ℝ, 0 ≤ x →
 ((mixedCandidateTailMatrix p L q lambda 0) - (mixedCandidateTailMatrix p L q lambda x)).det =
 (Matrix.of (fun i j => ∫ y in Iic x,
   mixedEnsembleF p L i y * mixedEnsembleG p L q lambda j y
   ∂(volume.restrict (Ioi (0 : ℝ))))).det
def Norm : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ), (∀ j, 0 ≤ lambda j) →
 ∀ x : ℝ, 0 ≤ x →
 ‖((theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda 0) -
    (theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda x)).det‖ =
 (∏ j : Fin p ⊕ Fin L, psiTailColumnFactor p L q lambda j) *
   |((mixedCandidateTailMatrix p L q lambda 0) - (mixedCandidateTailMatrix p L q lambda x)).det|
def Nonneg : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ), StrictMono lambda →
 (∀ j, 0 < lambda j) → ∀ x : ℝ, 0 ≤ x →
 0 ≤ (mixedCandidateTailMatrix p L q lambda 0 - mixedCandidateTailMatrix p L q lambda x).det
def LargestCDF : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ), StrictMono lambda →
 (∀ j, 0 < lambda j) → ∀ x : ℝ, 0 ≤ x →
 ((mixedCandidateEnsemble p L q lambda) {z | ∀ i, z i ≤ x}).toReal =
 ‖((theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda 0) -
    (theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda x)).det‖ /
 ‖(theorem1PsiMatrix (p+L) (p+L+q) L (by omega) (by omega) lambda 0).det‖
end
end SheafPsiCandidateLargest
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.mixedCandidateLowerMatrix_det_eq_restricted,`SheafPsiCandidateLargest.LowerDet),
 (`JinWishart.paperPsi_lower_det_norm,`SheafPsiCandidateLargest.Norm),
 (`JinWishart.mixedCandidateLowerMatrix_det_nonneg,`SheafPsiCandidateLargest.Nonneg),
 (`JinWishart.mixedCandidateEnsemble_all_le_eq_paperPsi_ratio,`SheafPsiCandidateLargest.LargestCDF)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Candidate Psi largest literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
