import JinWishartFormalization.CandidateTraceLaplaceClosed
import Lean
open MeasureTheory Matrix Finset Set JinWishart
namespace SheafCandidateTraceLaplaceClosed
noncomputable section
def Columns : Prop := ∀ (p L : ℕ) (lambda : Fin L → ℝ) (c : ℝ),
 (∏ j : Fin p ⊕ Fin L, weightedMixedColumnFactor p L lambda c j) =
 (∏ a : Fin p, (c^a.val)⁻¹) * (∏ j : Fin L, Real.exp (lambda j/c))
def Normalizer : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ), (∀ j, 0 ≤ lambda j) →
 (determinantMomentMatrix (volume.restrict (Ioi (0 : ℝ)))
   (mixedEnsembleF p L) (mixedEnsembleG p L q lambda)).det =
 (∏ j : Fin L, Real.exp (lambda j)) * (mixedNoncentralMomentMatrix q p L lambda).det
def Closed : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ), StrictMono lambda →
 (∀ j, 0 < lambda j) → ∀ s : ℝ, 0 ≤ s →
 (∫ z : Fin (p+L) → ℝ, Real.exp (-s * ∑ i, z i) ∂(mixedCandidateEnsemble p L q lambda)) =
 ((1+s)^((p+L)*(p+L+q)))⁻¹ * Real.exp (-s*(∑ j : Fin L, lambda j)/(1+s))
end
end SheafCandidateTraceLaplaceClosed
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.weightedMixedColumnFactor_prod,`SheafCandidateTraceLaplaceClosed.Columns),
 (`JinWishart.mixedEnsemble_momentMatrix_det,`SheafCandidateTraceLaplaceClosed.Normalizer),
 (`JinWishart.mixedCandidateEnsemble_trace_laplace_closed,`SheafCandidateTraceLaplaceClosed.Closed)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Candidate trace Laplace closed literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
