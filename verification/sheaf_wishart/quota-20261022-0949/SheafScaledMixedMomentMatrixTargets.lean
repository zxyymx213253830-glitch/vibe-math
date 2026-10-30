import JinWishartFormalization.ScaledMixedMomentMatrix
import Lean
open MeasureTheory Matrix Finset Set JinWishart
namespace SheafScaledMixedMomentMatrix
noncomputable section
def Entry : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ), (∀ j, 0 ≤ lambda j) →
 ∀ (c : ℝ), 0 < c → ∀ (i j : Fin (p+L)),
 weightedMixedMomentMatrix p L q lambda c i j =
 (c^(q+i.val+1))⁻¹ *
 weightedMixedColumnFactor p L lambda c ((finSumFinEquiv (m := p) (n := L)).symm j) *
 mixedNoncentralMomentMatrix q p L (fun b => lambda b/c)
   ((finSumFinEquiv (m := p) (n := L)).symm i)
   ((finSumFinEquiv (m := p) (n := L)).symm j)
def Determinant : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ), (∀ j, 0 ≤ lambda j) →
 ∀ c : ℝ, 0 < c →
 (weightedMixedMomentMatrix p L q lambda c).det =
 (∏ i : Fin (p+L), (c^(q+i.val+1))⁻¹) *
 (∏ j : Fin p ⊕ Fin L, weightedMixedColumnFactor p L lambda c j) *
 (mixedNoncentralMomentMatrix q p L (fun b => lambda b/c)).det
def Candidate : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ), StrictMono lambda →
 (∀ j, 0 < lambda j) → ∀ s : ℝ, 0 ≤ s →
 (∫ z : Fin (p+L) → ℝ, Real.exp (-s * ∑ i, z i) ∂(mixedCandidateEnsemble p L q lambda)) =
 ((∏ i : Fin (p+L), ((1+s)^(q+i.val+1))⁻¹) *
 (∏ j : Fin p ⊕ Fin L, weightedMixedColumnFactor p L lambda (1+s) j) *
 (mixedNoncentralMomentMatrix q p L (fun b => lambda b/(1+s))).det) /
 (determinantMomentMatrix (volume.restrict (Ioi (0 : ℝ)))
   (mixedEnsembleF p L) (mixedEnsembleG p L q lambda)).det
end
end SheafScaledMixedMomentMatrix
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.weightedMixedMomentMatrix_entry,`SheafScaledMixedMomentMatrix.Entry),
 (`JinWishart.weightedMixedMomentMatrix_det,`SheafScaledMixedMomentMatrix.Determinant),
 (`JinWishart.mixedCandidateEnsemble_trace_laplace_scaled_det,`SheafScaledMixedMomentMatrix.Candidate)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Scaled mixed matrix literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
