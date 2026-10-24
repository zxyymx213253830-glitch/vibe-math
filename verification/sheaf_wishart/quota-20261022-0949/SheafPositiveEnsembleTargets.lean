import JinWishartFormalization.PositiveDeterminantEnsembleCount
import Lean
open MeasureTheory JinWishart Polynomial
namespace SheafPositiveEnsemble
noncomputable section
def Total : Prop := ∀ (n : ℕ) (μ : Measure ℝ) [SigmaFinite μ] (f g : Fin n → ℝ → ℝ),
 (∀ i j,Integrable (fun y => f i y*g j y) μ) → (∀ z,0≤determinantProduct f g z) →
 determinantEnsembleMeasure μ f g Set.univ=ENNReal.ofReal ((n.factorial : ℝ)*(determinantMomentMatrix μ f g).det)
def Count : Prop := ∀ (n : ℕ) (μ : Measure ℝ) [SigmaFinite μ] (f g : Fin n → ℝ → ℝ),
 (∀ i j,Integrable (fun y => f i y*g j y) μ) → (∀ z,0≤determinantProduct f g z) →
 ∀ E : Set ℝ,MeasurableSet E → ∀ k : ℕ,k≤n →
 determinantEnsembleMeasure μ f g {z | coordinateMembershipCount E z=k}=
 ENNReal.ofReal ((n.factorial : ℝ)*((rowAffinePolynomialMatrix
 (Matrix.of (fun i j => ∫ y in E,f i y*g j y ∂μ))
 (Matrix.of (fun i j => ∫ y in Eᶜ,f i y*g j y ∂μ))).det).coeff k)
def Probability : Prop := ∀ (n : ℕ) (μ : Measure ℝ) [SigmaFinite μ] (f g : Fin n → ℝ → ℝ),
 (∀ i j,Integrable (fun y => f i y*g j y) μ) → (∀ z,0≤determinantProduct f g z) →
 0<(determinantMomentMatrix μ f g).det →
 IsProbabilityMeasure (normalizedDeterminantEnsemble μ f g) ∧
 ∀ E : Set ℝ,MeasurableSet E → ∀ k : ℕ,k≤n →
 ((normalizedDeterminantEnsemble μ f g) {z | coordinateMembershipCount E z=k}).toReal=
 ((rowAffinePolynomialMatrix (Matrix.of (fun i j => ∫ y in E,f i y*g j y ∂μ))
 (Matrix.of (fun i j => ∫ y in Eᶜ,f i y*g j y ∂μ))).det).coeff k/(determinantMomentMatrix μ f g).det
end
end SheafPositiveEnsemble
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.determinantEnsemble_total_mass,`SheafPositiveEnsemble.Total),
 (`JinWishart.determinantEnsemble_count_mass,`SheafPositiveEnsemble.Count),
 (`JinWishart.normalizedDeterminantEnsemble_probability_count,`SheafPositiveEnsemble.Probability)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Positive ensemble literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
