import JinWishartFormalization.MixedCandidateExtremeEvents
import Lean
open MeasureTheory Matrix Polynomial Set JinWishart
namespace SheafCandidateExtremeEvents
noncomputable section
def Coeff0 : Prop := ∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ),
 ((rowAffinePolynomialMatrix A B).det).coeff 0 = B.det
def Count0 : Prop := ∀ (n : ℕ) (E : Set ℝ) (z : Fin n → ℝ),
 coordinateMembershipCount Eᶜ z = 0 ↔ ∀ i, z i ∈ E
def AllIn : Prop := ∀ (n : ℕ) (μ : Measure ℝ) [SigmaFinite μ] (f g : Fin n → ℝ → ℝ),
 (∀ i j, Integrable (fun y => f i y*g j y) μ) →
 (∀ z, 0 ≤ determinantProduct f g z) → 0 < (determinantMomentMatrix μ f g).det →
 ∀ (E : Set ℝ), MeasurableSet E →
 ((normalizedDeterminantEnsemble μ f g) {z | ∀ i, z i ∈ E}).toReal =
 (Matrix.of (fun i j => ∫ y in E, f i y*g j y ∂μ)).det / (determinantMomentMatrix μ f g).det
def CandidateAll : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ), StrictMono lambda →
 (∀ j, 0 < lambda j) → ∀ (E : Set ℝ), MeasurableSet E →
 ((mixedCandidateEnsemble p L q lambda) {z | ∀ i, z i ∈ E}).toReal =
 (Matrix.of (fun i j => ∫ y in E, mixedEnsembleF p L i y * mixedEnsembleG p L q lambda j y
   ∂(volume.restrict (Ioi (0 : ℝ))))).det /
 (determinantMomentMatrix (volume.restrict (Ioi (0 : ℝ)))
   (mixedEnsembleF p L) (mixedEnsembleG p L q lambda)).det
def AllLe : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ), StrictMono lambda →
 (∀ j, 0 < lambda j) → ∀ t : ℝ,
 ((mixedCandidateEnsemble p L q lambda) {z | ∀ i, z i ≤ t}).toReal =
 (Matrix.of (fun i j => ∫ y in Iic t, mixedEnsembleF p L i y * mixedEnsembleG p L q lambda j y
   ∂(volume.restrict (Ioi (0 : ℝ))))).det /
 (determinantMomentMatrix (volume.restrict (Ioi (0 : ℝ)))
   (mixedEnsembleF p L) (mixedEnsembleG p L q lambda)).det
def AllGt : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ), StrictMono lambda →
 (∀ j, 0 < lambda j) → ∀ t : ℝ,
 ((mixedCandidateEnsemble p L q lambda) {z | ∀ i, t < z i}).toReal =
 (Matrix.of (fun i j => ∫ y in Ioi t, mixedEnsembleF p L i y * mixedEnsembleG p L q lambda j y
   ∂(volume.restrict (Ioi (0 : ℝ))))).det /
 (determinantMomentMatrix (volume.restrict (Ioi (0 : ℝ)))
   (mixedEnsembleF p L) (mixedEnsembleG p L q lambda)).det
end
end SheafCandidateExtremeEvents
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.coeff_zero_rowAffine_det,`SheafCandidateExtremeEvents.Coeff0),
 (`JinWishart.coordinateMembershipCount_compl_eq_zero_iff,`SheafCandidateExtremeEvents.Count0),
 (`JinWishart.normalizedDeterminantEnsemble_allIn,`SheafCandidateExtremeEvents.AllIn),
 (`JinWishart.mixedCandidateEnsemble_allIn,`SheafCandidateExtremeEvents.CandidateAll),
 (`JinWishart.mixedCandidateEnsemble_all_le,`SheafCandidateExtremeEvents.AllLe),
 (`JinWishart.mixedCandidateEnsemble_all_gt,`SheafCandidateExtremeEvents.AllGt)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Candidate extreme events literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
