import JinWishartFormalization.FixedRankPositiveMinimum
import Lean
open Matrix MeasureTheory ProbabilityTheory
namespace SheafPositiveMinimum
noncomputable section
def Prefix : Prop := ∀ {n : ℕ} (f : Fin n → ℝ), Antitone f → ∀ i : Fin n,
 0<f i ↔ i.val<(Finset.univ.filter (fun j => 0<f j)).card
def Minimum : Prop := ∀ {n : ℕ} (f : Fin n → ℝ), Antitone f → ∀ i : Fin n,
 (Finset.univ.filter (fun j => 0<f j)).card=i.val+1 →
 0<f i ∧ ∀ j,0<f j → f i≤f j
def Cardinal : Prop := ∀ {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℂ),
 (Finset.univ.filter (fun i => 0<(JinWishart.complexGram_posSemidef X).1.eigenvalues₀ i)).card=X.rank
def Actual : Prop := ∀ {m p n : ℕ} (B : Matrix (Fin p) (Fin n) ℂ)
 (M : Matrix (Fin m) (Fin n) ℂ), 0<min m (Matrix.fromRows B M).rank →
 ∃ i : Fin (Fintype.card (Fin n)),
 i.val+1=min m (Matrix.fromRows B M).rank ∧
 Measurable (JinWishart.actualCorrelatedEigenvalue B M i) ∧
 ∀ᵐ z ∂stdGaussian (JinWishart.ComplexSample (m := m) (n := p)),
 0<JinWishart.actualCorrelatedEigenvalue B M i z ∧
 ∀ j,0<JinWishart.actualCorrelatedEigenvalue B M j z →
 JinWishart.actualCorrelatedEigenvalue B M i z≤JinWishart.actualCorrelatedEigenvalue B M j z
end
end SheafPositiveMinimum
open Lean Meta in
#eval show MetaM Unit from do
 for (target,expected) in [
 (`JinWishart.antitone_positive_iff_lt_count,`SheafPositiveMinimum.Prefix),
 (`JinWishart.antitone_min_positive_at_count,`SheafPositiveMinimum.Minimum),
 (`JinWishart.gram_positive_modes_card_eq_rank,`SheafPositiveMinimum.Cardinal),
 (`JinWishart.exists_actualCorrelated_smallest_positive_coordinate,`SheafPositiveMinimum.Actual)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels target)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels expected)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF target type differs: {target}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
