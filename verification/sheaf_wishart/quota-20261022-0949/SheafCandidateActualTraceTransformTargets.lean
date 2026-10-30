import JinWishartFormalization.CandidateActualTraceTransform
import Lean
open MeasureTheory Matrix ProbabilityTheory Finset JinWishart
namespace SheafCandidateActualTraceTransform
noncomputable section
def Actual : Prop := ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) (s : ℝ), 0 ≤ s →
 (∫ z : ComplexSample (m := m) (n := n),
    Real.exp (-s * ∑ j : Fin n, (complexGram (complexSampleMatrix z+M) j j).re)
    ∂stdGaussian (ComplexSample (m := m) (n := n))) =
 ((1+s)^(m*n))⁻¹ * Real.exp (-s*(∑ a : Fin m × Fin n, ‖M a.1 a.2‖^2)/(1+s))
def Equal : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ), StrictMono lambda →
 (∀ j, 0 < lambda j) → ∀ (M : Matrix (Fin (p+L+q)) (Fin (p+L)) ℂ),
 ((∑ a : Fin (p+L+q) × Fin (p+L), ‖M a.1 a.2‖^2) = ∑ j : Fin L, lambda j) →
 ∀ s : ℝ, 0 ≤ s →
 (∫ z : Fin (p+L) → ℝ, Real.exp (-s * ∑ i, z i) ∂(mixedCandidateEnsemble p L q lambda)) =
 (∫ z : ComplexSample (m := p+L+q) (n := p+L),
    Real.exp (-s * ∑ j : Fin (p+L), (complexGram (complexSampleMatrix z+M) j j).re)
    ∂stdGaussian (ComplexSample (m := p+L+q) (n := p+L)))
end
end SheafCandidateActualTraceTransform
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.actualNoncentralGram_trace_laplace,`SheafCandidateActualTraceTransform.Actual),
 (`JinWishart.candidate_actual_trace_laplace_equal,`SheafCandidateActualTraceTransform.Equal)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Candidate actual trace transform literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
