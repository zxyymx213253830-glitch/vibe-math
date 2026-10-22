import JinWishartFormalization.WidePositiveCoordinate
import Lean
open Matrix MeasureTheory ProbabilityTheory
namespace SheafWidePositive
noncomputable section
def Deterministic : Prop := ∀ {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℂ) (hm : 0<m)
 (i : Fin (Fintype.card (Fin n))),i.val+1=m → X.rank=m →
 (0<(JinWishart.complexGram_posSemidef X).1.eigenvalues₀ i ∧
 (JinWishart.complexGram_posSemidef X).1.eigenvalues₀ i=JinWishart.gramSmallestValue Xᴴ hm)
def Actual : Prop := ∀ (m n : ℕ) (hm : 0<m) (_hmn : m≤n)
 (M : Matrix (Fin m) (Fin n) ℂ) (i : Fin (Fintype.card (Fin n))),i.val+1=m →
 ∀ᵐ z ∂stdGaussian (JinWishart.ComplexSample (m := m) (n := n)),
 0<JinWishart.complexNoncentralSampleEigenvalue M i z ∧
 JinWishart.complexNoncentralSampleEigenvalue M i z=
 JinWishart.gramSmallestValue (JinWishart.complexSampleMatrix z+M)ᴴ hm
def Moment : Prop := ∀ (m n : ℕ) (hm : 0<m) (_hmn : m≤n)
 (M : Matrix (Fin m) (Fin n) ℂ) (i : Fin (Fintype.card (Fin n))),i.val+1=m →
 ∀ p : ℝ,0<p → (Integrable (fun z=>((JinWishart.complexNoncentralSampleEigenvalue M i z)⁻¹)^p)
 (stdGaussian (JinWishart.ComplexSample (m := m) (n := n))) ↔ p<((n-m+1 : ℕ) : ℝ))
def Top : Prop := ∀ (m n : ℕ) (hm : 0<m) (_hmn : m≤n)
 (M : Matrix (Fin m) (Fin n) ℂ) (i : Fin (Fintype.card (Fin n))),i.val+1=m →
 ∀ p : ℝ,((n-m+1 : ℕ) : ℝ)≤p →
 (∫⁻ z,ENNReal.ofReal (((JinWishart.complexNoncentralSampleEigenvalue M i z)⁻¹)^p)
 ∂stdGaussian (JinWishart.ComplexSample (m := m) (n := n)))=⊤
end
end SheafWidePositive
open Lean Meta in
#eval show MetaM Unit from do
 for (target,expected) in [
 (`JinWishart.gram_full_row_rank_coordinate_eq_rowMinimum,`SheafWidePositive.Deterministic),
 (`JinWishart.actualWide_fixed_positive_coordinate_ae,`SheafWidePositive.Actual),
 (`JinWishart.actualWide_fixed_positive_inverse_realMoment_integrable_iff,`SheafWidePositive.Moment),
 (`JinWishart.actualWide_fixed_positive_inverse_realMoment_lintegral_eq_top,`SheafWidePositive.Top)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels target)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels expected)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF target type differs: {target}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
