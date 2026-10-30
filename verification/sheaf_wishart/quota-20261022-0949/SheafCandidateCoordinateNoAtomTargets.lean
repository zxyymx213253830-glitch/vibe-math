import JinWishartFormalization.CandidateCoordinateNoAtom
import Lean
open MeasureTheory Set JinWishart
namespace SheafCandidateCoordinateNoAtom
noncomputable section
def Atom : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ) (i : Fin (p+L)) (x : ℝ),
 mixedCandidateEnsemble p L q lambda {z | z i = x} = 0
def Ne : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ) (x : ℝ),
 ∀ᵐ z ∂mixedCandidateEnsemble p L q lambda, ∀ i, z i ≠ x
def AllLe : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ) (x : ℝ),
 mixedCandidateEnsemble p L q lambda {z | ∀ i, z i ≤ x} =
 mixedCandidateEnsemble p L q lambda {z | ∀ i, z i < x}
def ExistsLe : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ) (x : ℝ),
 mixedCandidateEnsemble p L q lambda {z | ∃ i, z i ≤ x} =
 mixedCandidateEnsemble p L q lambda {z | ∃ i, z i < x}
def AllGe : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ) (x : ℝ),
 mixedCandidateEnsemble p L q lambda {z | ∀ i, x ≤ z i} =
 mixedCandidateEnsemble p L q lambda {z | ∀ i, x < z i}
def ExistsGe : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ) (x : ℝ),
 mixedCandidateEnsemble p L q lambda {z | ∃ i, x ≤ z i} =
 mixedCandidateEnsemble p L q lambda {z | ∃ i, x < z i}
end
end SheafCandidateCoordinateNoAtom
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.mixedCandidateEnsemble_coordinate_noAtom,`SheafCandidateCoordinateNoAtom.Atom),
 (`JinWishart.mixedCandidateEnsemble_coordinates_ne_ae,`SheafCandidateCoordinateNoAtom.Ne),
 (`JinWishart.mixedCandidateEnsemble_all_le_eq_all_lt,`SheafCandidateCoordinateNoAtom.AllLe),
 (`JinWishart.mixedCandidateEnsemble_exists_le_eq_exists_lt,`SheafCandidateCoordinateNoAtom.ExistsLe),
 (`JinWishart.mixedCandidateEnsemble_all_ge_eq_all_gt,`SheafCandidateCoordinateNoAtom.AllGe),
 (`JinWishart.mixedCandidateEnsemble_exists_ge_eq_exists_gt,`SheafCandidateCoordinateNoAtom.ExistsGe)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Candidate coordinate no-atom literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
