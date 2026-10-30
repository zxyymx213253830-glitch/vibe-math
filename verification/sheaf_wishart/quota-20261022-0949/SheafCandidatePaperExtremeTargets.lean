import JinWishartFormalization.CandidatePaperExtremeCDF
import Lean
open MeasureTheory Matrix Set JinWishart
namespace SheafCandidatePaperExtreme
noncomputable section
def Largest : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ), StrictMono lambda →
 (∀ j, 0 < lambda j) → ∀ x : ℝ, 0 ≤ x →
 theorem2CdfCandidate (p+L) (p+L+q) L (by omega) (by omega) lambda x =
 ((mixedCandidateEnsemble p L q lambda) {z | ∀ i, z i ≤ x}).toReal
def Smallest : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ), StrictMono lambda →
 (∀ j, 0 < lambda j) → ∀ x : ℝ, 0 ≤ x →
 theorem1CdfCandidate (p+L) (p+L+q) L (by omega) (by omega) lambda x =
 ((mixedCandidateEnsemble p L q lambda) {z | ∃ i, z i ≤ x}).toReal
end
end SheafCandidatePaperExtreme
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.theorem2Candidate_eq_mixedCandidate_all_le,`SheafCandidatePaperExtreme.Largest),
 (`JinWishart.theorem1Candidate_eq_mixedCandidate_exists_le,`SheafCandidatePaperExtreme.Smallest)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Candidate paper extreme literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
