import JinWishartFormalization.CandidateSpectralTraceLaw
import Lean
open Matrix MeasureTheory ProbabilityTheory Finset JinWishart
namespace SheafCandidateSpectralTraceLaw
noncomputable section
def Law : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ), StrictMono lambda →
 (∀ j, 0 < lambda j) → ∀ (M : Matrix (Fin (p+L+q)) (Fin (p+L)) ℂ),
 ((∑ a : Fin (p+L+q) × Fin (p+L), ‖M a.1 a.2‖^2) = ∑ j : Fin L, lambda j) →
 (mixedCandidateEnsemble p L q lambda).map (fun z => ∑ i, z i) =
 (stdGaussian (ComplexSample (m := p+L+q) (n := p+L))).map
   (fun z => ∑ i, complexNoncentralSampleEigenvalue M i z)
def MeanSum : Prop := ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ),
 (∑ i : Fin M.rank, meanPositiveNoncentrality M i) =
 ∑ a : Fin m × Fin n, ‖M a.1 a.2‖^2
def Spectral : Prop := ∀ (p L q : ℕ) (lambda : Fin L → ℝ), StrictMono lambda →
 (∀ j, 0 < lambda j) → ∀ (M : Matrix (Fin (p+L+q)) (Fin (p+L)) ℂ)
 (e : Fin L ≃ Fin M.rank), (∀ j, lambda j = meanPositiveNoncentrality M (e j)) →
 (mixedCandidateEnsemble p L q lambda).map (fun z => ∑ i, z i) =
 (stdGaussian (ComplexSample (m := p+L+q) (n := p+L))).map
   (fun z => ∑ i, complexNoncentralSampleEigenvalue M i z)
end
end SheafCandidateSpectralTraceLaw
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.candidate_actual_eigenvalue_sum_law_equal,`SheafCandidateSpectralTraceLaw.Law),
 (`JinWishart.meanPositiveNoncentrality_sum_eq_energy,`SheafCandidateSpectralTraceLaw.MeanSum),
 (`JinWishart.candidate_actual_eigenvalue_sum_law_of_mean_spectrum,`SheafCandidateSpectralTraceLaw.Spectral)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Candidate spectral trace law literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
