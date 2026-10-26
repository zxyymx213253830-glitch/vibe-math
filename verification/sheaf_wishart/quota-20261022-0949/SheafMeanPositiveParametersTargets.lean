import JinWishartFormalization.MeanPositiveNoncentralParameters
import Lean
open Matrix MeasureTheory ProbabilityTheory JinWishart
namespace SheafMeanPositiveParameters
noncomputable section
def Positive : Prop := ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) (i : Fin M.rank),
 0 < meanPositiveNoncentrality M i
def Ordered : Prop := ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ),
 Antitone (meanPositiveNoncentrality M)
def ZeroTail : Prop := ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ)
 (i : Fin (Fintype.card (Fin n))),
 (complexGram_posSemidef M).1.eigenvalues₀ i = 0 ↔ M.rank ≤ i.val
def Reconstruct : Prop := ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ)
 (i : Fin (Fintype.card (Fin n))),
 (complexGram_posSemidef M).1.eigenvalues₀ i =
 if h : i.val < M.rank then meanPositiveNoncentrality M ⟨i.val,h⟩ else 0
def StrictPaper : Prop := ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ),
 StrictAnti (meanPositiveNoncentrality M) →
 ∃ p : OrderedPositiveNoncentralSpectrum M.rank, p.values = meanPositiveNoncentrality M
def Law : Prop := ∀ {m n : ℕ} (M N : Matrix (Fin m) (Fin n) ℂ)
 (hRank : M.rank = N.rank),
 (∀ i : Fin M.rank, meanPositiveNoncentrality M i =
   meanPositiveNoncentrality N (Fin.cast hRank i)) →
 (stdGaussian (ComplexSample (m := m) (n := n))).map (paperJointSpectrum M) =
 (stdGaussian (ComplexSample (m := m) (n := n))).map (paperJointSpectrum N)
end
end SheafMeanPositiveParameters
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.meanPositiveNoncentrality_pos,`SheafMeanPositiveParameters.Positive),
 (`JinWishart.meanPositiveNoncentrality_antitone,`SheafMeanPositiveParameters.Ordered),
 (`JinWishart.meanGram_eigenvalue_zero_iff_rank_le_index,`SheafMeanPositiveParameters.ZeroTail),
 (`JinWishart.meanGram_eigenvalue_positive_parameter_or_zero,`SheafMeanPositiveParameters.Reconstruct),
 (`JinWishart.exists_paper_positiveNoncentralSpectrum_of_strict,`SheafMeanPositiveParameters.StrictPaper),
 (`JinWishart.actualNoncentral_paperJointSpectrum_law_of_positive_parameters,`SheafMeanPositiveParameters.Law)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Mean positive noncentral parameter literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
