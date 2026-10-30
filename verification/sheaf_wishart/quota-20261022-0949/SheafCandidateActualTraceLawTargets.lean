import JinWishartFormalization.NonnegativeScalarLaplaceUniqueness
import Lean
open MeasureTheory Matrix ProbabilityTheory Finset JinWishart
namespace SheafCandidateActualTraceLaw
noncomputable section
def Uniqueness : Prop := ∀ {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν],
 (∀ᵐ x ∂μ, 0 ≤ x) → (∀ᵐ x ∂ν, 0 ≤ x) →
 (∀ s : ℝ, 0 ≤ s → (∫ x, Real.exp (-s*x) ∂μ) = ∫ x, Real.exp (-s*x) ∂ν) → μ = ν
def MapUniqueness {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] : Prop :=
 ∀ {μ : Measure Ω} {ν : Measure Ω'} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
 {X : Ω → ℝ} {Y : Ω' → ℝ}, AEMeasurable X μ → AEMeasurable Y ν →
 (∀ᵐ x ∂μ, 0 ≤ X x) → (∀ᵐ y ∂ν, 0 ≤ Y y) →
 (∀ s : ℝ, 0 ≤ s → (∫ x, Real.exp (-s*X x) ∂μ) = ∫ y, Real.exp (-s*Y y) ∂ν) →
 μ.map X = ν.map Y
def Support : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ),
 ∀ᵐ z ∂mixedCandidateEnsemble p L q lambda, ∀ i, 0 < z i
def Law : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ), StrictMono lambda →
 (∀ j, 0 < lambda j) → ∀ (M : Matrix (Fin (p+L+q)) (Fin (p+L)) ℂ),
 ((∑ a : Fin (p+L+q) × Fin (p+L), ‖M a.1 a.2‖^2) = ∑ j : Fin L, lambda j) →
 (mixedCandidateEnsemble p L q lambda).map (fun z => ∑ i, z i) =
 (stdGaussian (ComplexSample (m := p+L+q) (n := p+L))).map
   (fun z => ∑ j : Fin (p+L), (complexGram (complexSampleMatrix z+M) j j).re)
end
end SheafCandidateActualTraceLaw
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.nonnegative_measure_eq_of_laplace_eq,`SheafCandidateActualTraceLaw.Uniqueness),
 (`JinWishart.map_eq_of_nonnegative_laplace_eq,`SheafCandidateActualTraceLaw.MapUniqueness),
 (`JinWishart.mixedCandidateEnsemble_coordinates_positive_ae,`SheafCandidateActualTraceLaw.Support),
 (`JinWishart.candidate_actual_trace_law_equal,`SheafCandidateActualTraceLaw.Law)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Candidate actual trace law literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
