import JinWishartFormalization.CandidateTraceMoments
import Lean
open Matrix MeasureTheory ProbabilityTheory Finset JinWishart
namespace SheafCandidateTraceMoments
noncomputable section
def Transfer : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ), StrictMono lambda →
 (∀ j, 0 < lambda j) → ∀ (M : Matrix (Fin (p+L+q)) (Fin (p+L)) ℂ),
 ((∑ a : Fin (p+L+q) × Fin (p+L), ‖M a.1 a.2‖^2) = ∑ j : Fin L, lambda j) →
 ∀ (F : ℝ → ℝ), Continuous F →
 (∫ z : Fin (p+L) → ℝ, F (∑ i, z i) ∂(mixedCandidateEnsemble p L q lambda)) =
 (∫ z : ComplexSample (m := p+L+q) (n := p+L),
    F ((complexGram (complexSampleMatrix z+M)).trace.re)
    ∂stdGaussian (ComplexSample (m := p+L+q) (n := p+L)))
def IntegrableTransfer : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ), StrictMono lambda →
 (∀ j, 0 < lambda j) → ∀ (M : Matrix (Fin (p+L+q)) (Fin (p+L)) ℂ),
 ((∑ a : Fin (p+L+q) × Fin (p+L), ‖M a.1 a.2‖^2) = ∑ j : Fin L, lambda j) →
 ∀ (F : ℝ → ℝ), Continuous F →
 Integrable (fun z : ComplexSample (m := p+L+q) (n := p+L) =>
   F ((complexGram (complexSampleMatrix z+M)).trace.re)) (stdGaussian _) →
 Integrable (fun z : Fin (p+L) → ℝ => F (∑ i, z i)) (mixedCandidateEnsemble p L q lambda)
def IntegrableMean : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ), StrictMono lambda →
 (∀ j, 0 < lambda j) → ∀ (M : Matrix (Fin (p+L+q)) (Fin (p+L)) ℂ),
 ((∑ a : Fin (p+L+q) × Fin (p+L), ‖M a.1 a.2‖^2) = ∑ j : Fin L, lambda j) →
 Integrable (fun z : Fin (p+L) → ℝ => ∑ i, z i) (mixedCandidateEnsemble p L q lambda)
def IntegrableCentered : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ), StrictMono lambda →
 (∀ j, 0 < lambda j) → ∀ (M : Matrix (Fin (p+L+q)) (Fin (p+L)) ℂ),
 ((∑ a : Fin (p+L+q) × Fin (p+L), ‖M a.1 a.2‖^2) = ∑ j : Fin L, lambda j) →
 ∀ T : ℝ, Integrable (fun z : Fin (p+L) → ℝ => ((∑ i, z i)-T)^2)
   (mixedCandidateEnsemble p L q lambda)
def Mean : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ), StrictMono lambda →
 (∀ j, 0 < lambda j) → ∀ (M : Matrix (Fin (p+L+q)) (Fin (p+L)) ℂ),
 ((∑ a : Fin (p+L+q) × Fin (p+L), ‖M a.1 a.2‖^2) = ∑ j : Fin L, lambda j) →
 (∫ z : Fin (p+L) → ℝ, ∑ i, z i ∂(mixedCandidateEnsemble p L q lambda)) =
 (((p+L)*(p+L+q) : ℕ) : ℝ) + ∑ j : Fin L, lambda j
def Centered : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ), StrictMono lambda →
 (∀ j, 0 < lambda j) → ∀ (M : Matrix (Fin (p+L+q)) (Fin (p+L)) ℂ),
 ((∑ a : Fin (p+L+q) × Fin (p+L), ‖M a.1 a.2‖^2) = ∑ j : Fin L, lambda j) →
 (∫ z : Fin (p+L) → ℝ,
   ((∑ i, z i) - (((p+L)*(p+L+q) : ℕ) : ℝ) - ∑ j : Fin L, lambda j)^2
   ∂(mixedCandidateEnsemble p L q lambda)) =
 (((p+L)*(p+L+q) : ℕ) : ℝ) + 2*(∑ j : Fin L, lambda j)
end
end SheafCandidateTraceMoments
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.candidate_actual_trace_integral_transfer,`SheafCandidateTraceMoments.Transfer),
 (`JinWishart.candidate_actual_trace_integrable_transfer,`SheafCandidateTraceMoments.IntegrableTransfer),
 (`JinWishart.candidate_trace_integrable,`SheafCandidateTraceMoments.IntegrableMean),
 (`JinWishart.candidate_trace_centered_sq_integrable,`SheafCandidateTraceMoments.IntegrableCentered),
 (`JinWishart.candidate_trace_mean,`SheafCandidateTraceMoments.Mean),
 (`JinWishart.candidate_trace_centered_second_moment,`SheafCandidateTraceMoments.Centered)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Candidate trace moments literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
