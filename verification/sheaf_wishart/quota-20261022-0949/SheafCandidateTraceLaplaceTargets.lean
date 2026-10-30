import JinWishartFormalization.CandidateTraceLaplace
import Lean
open MeasureTheory Matrix Finset Set JinWishart
namespace SheafCandidateTraceLaplace
noncomputable section
def WeightedIntegrable : Prop := ∀ (u : ℝ → ℝ) (s : ℝ), 0 ≤ s →
 Integrable u (volume.restrict (Ioi (0 : ℝ))) →
 Integrable (fun y => Real.exp (-s*y)*u y) (volume.restrict (Ioi (0 : ℝ)))
def GeneralAE : Prop := ∀ {n : ℕ} {μ : Measure ℝ} [SigmaFinite μ]
 (f g : Fin n → ℝ → ℝ) (s : ℝ),
 (∀ i j, Integrable (fun y => f i y * (Real.exp (-s*y) * g j y)) μ) →
 (∀ z, 0 ≤ determinantProduct f g z) →
 AEMeasurable (fun z => ENNReal.ofReal (determinantProduct f g z))
    (Measure.pi (fun _ : Fin n => μ)) →
 0 < (determinantMomentMatrix μ f g).det →
 (∫ z : Fin n → ℝ, Real.exp (-s * ∑ i, z i) ∂(normalizedDeterminantEnsemble μ f g)) =
 (Matrix.of (fun i j => ∫ y, f i y * (Real.exp (-s*y) * g j y) ∂μ)).det /
 (determinantMomentMatrix μ f g).det
def Candidate : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ), StrictMono lambda →
 (∀ j, 0 < lambda j) → ∀ s : ℝ, 0 ≤ s →
 (∫ z : Fin (p+L) → ℝ, Real.exp (-s * ∑ i, z i) ∂(mixedCandidateEnsemble p L q lambda)) =
 (Matrix.of (fun i j => ∫ y, mixedEnsembleF p L i y *
   (Real.exp (-s*y) * mixedEnsembleG p L q lambda j y)
   ∂(volume.restrict (Ioi (0 : ℝ))))).det /
 (determinantMomentMatrix (volume.restrict (Ioi (0 : ℝ)))
   (mixedEnsembleF p L) (mixedEnsembleG p L q lambda)).det
end
end SheafCandidateTraceLaplace
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.integrable_exp_weighted_positive,`SheafCandidateTraceLaplace.WeightedIntegrable),
 (`JinWishart.normalizedDeterminantEnsemble_trace_laplace_ae,`SheafCandidateTraceLaplace.GeneralAE),
 (`JinWishart.mixedCandidateEnsemble_trace_laplace_det,`SheafCandidateTraceLaplace.Candidate)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Candidate trace Laplace literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
