import JinWishartFormalization.WeightedAndreief
import Lean
open MeasureTheory Matrix Finset JinWishart
namespace SheafWeightedAndreief
noncomputable section
def Weighted : Prop := ∀ {n : ℕ} {μ : Measure ℝ} [SigmaFinite μ]
 (f g : Fin n → ℝ → ℝ) (w : ℝ → ℝ),
 (∀ i j, Integrable (fun y => f i y * (w y * g j y)) μ) →
 (∫ z : Fin n → ℝ, (∏ i, w (z i)) * determinantProduct f g z
   ∂(Measure.pi (fun _ : Fin n => μ))) =
 (n.factorial : ℝ) * (Matrix.of (fun i j => ∫ y, f i y * (w y * g j y) ∂μ)).det
def Expectation : Prop := ∀ {n : ℕ} {μ : Measure ℝ} [SigmaFinite μ]
 (f g : Fin n → ℝ → ℝ) (w : ℝ → ℝ),
 (∀ i j, Integrable (fun y => f i y * (w y * g j y)) μ) →
 (∀ z, 0 ≤ determinantProduct f g z) →
 Measurable (fun z => ENNReal.ofReal (determinantProduct f g z)) →
 0 < (determinantMomentMatrix μ f g).det →
 (∫ z : Fin n → ℝ, ∏ i, w (z i) ∂(normalizedDeterminantEnsemble μ f g)) =
 (Matrix.of (fun i j => ∫ y, f i y * (w y * g j y) ∂μ)).det /
 (determinantMomentMatrix μ f g).det
def ExpWeighted : Prop := ∀ {n : ℕ} {μ : Measure ℝ} [SigmaFinite μ]
 (f g : Fin n → ℝ → ℝ) (s : ℝ),
 (∀ i j, Integrable (fun y => f i y * (Real.exp (-s*y) * g j y)) μ) →
 (∫ z : Fin n → ℝ, Real.exp (-s * ∑ i, z i) * determinantProduct f g z
   ∂(Measure.pi (fun _ : Fin n => μ))) =
 (n.factorial : ℝ) * (Matrix.of (fun i j => ∫ y, f i y * (Real.exp (-s*y) * g j y) ∂μ)).det
def Laplace : Prop := ∀ {n : ℕ} {μ : Measure ℝ} [SigmaFinite μ]
 (f g : Fin n → ℝ → ℝ) (s : ℝ),
 (∀ i j, Integrable (fun y => f i y * (Real.exp (-s*y) * g j y)) μ) →
 (∀ z, 0 ≤ determinantProduct f g z) →
 Measurable (fun z => ENNReal.ofReal (determinantProduct f g z)) →
 0 < (determinantMomentMatrix μ f g).det →
 (∫ z : Fin n → ℝ, Real.exp (-s * ∑ i, z i) ∂(normalizedDeterminantEnsemble μ f g)) =
 (Matrix.of (fun i j => ∫ y, f i y * (Real.exp (-s*y) * g j y) ∂μ)).det /
 (determinantMomentMatrix μ f g).det
end
end SheafWeightedAndreief
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.weighted_andreief,`SheafWeightedAndreief.Weighted),
 (`JinWishart.normalizedDeterminantEnsemble_product_expectation,`SheafWeightedAndreief.Expectation),
 (`JinWishart.exp_sum_weighted_andreief,`SheafWeightedAndreief.ExpWeighted),
 (`JinWishart.normalizedDeterminantEnsemble_trace_laplace,`SheafWeightedAndreief.Laplace)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Weighted Andreief literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
