import JinWishartFormalization.SplitAndreiefCountCoefficients
import Lean
open MeasureTheory JinWishart Polynomial
namespace SheafSplitCount
noncomputable section
def Generate : Prop := ∀ (n : ℕ) (μ : Measure ℝ) [SigmaFinite μ] (f g : Fin n → ℝ → ℝ),
 (∀ i j,Integrable (fun y => f i y*g j y) μ) → ∀ E : Set ℝ,MeasurableSet E → ∀ t : ℝ,
 Matrix.det (fun i j => t*(∫ y in E,f i y*g j y ∂μ)+∫ y in Eᶜ,f i y*g j y ∂μ)=
 (1/(n.factorial : ℝ))*∫ z : Fin n → ℝ,t^(coordinateMembershipCount E z)*
 (Matrix.of (fun i j => f i (z j))).det*(Matrix.of (fun i j => g i (z j))).det
 ∂(Measure.pi (fun _ : Fin n => μ))
def Meas : Prop := ∀ (n : ℕ) (E : Set ℝ),MeasurableSet E → Measurable (coordinateMembershipCount (n := n) E)
def Int : Prop := ∀ (n : ℕ) (μ : Measure ℝ) [SigmaFinite μ] (f g : Fin n → ℝ → ℝ),
 (∀ i j,Integrable (fun y => f i y*g j y) μ) → Integrable (fun z : Fin n → ℝ =>
 (Matrix.of (fun i j => f i (z j))).det*(Matrix.of (fun i j => g i (z j))).det)
 (Measure.pi (fun _ : Fin n => μ))
def Poly : Prop := ∀ (n : ℕ) (μ : Measure ℝ) [SigmaFinite μ] (f g : Fin n → ℝ → ℝ),
 (∀ i j,Integrable (fun y => f i y*g j y) μ) → ∀ E : Set ℝ,MeasurableSet E →
 (rowAffinePolynomialMatrix (Matrix.of (fun i j => ∫ y in E,f i y*g j y ∂μ))
 (Matrix.of (fun i j => ∫ y in Eᶜ,f i y*g j y ∂μ))).det=
 ∑ k ∈ Finset.range (n+1),Polynomial.C ((1/(n.factorial : ℝ))*countDeterminantMoment f g μ E k)*Polynomial.X^k
def Coeff : Prop := ∀ (n : ℕ) (μ : Measure ℝ) [SigmaFinite μ] (f g : Fin n → ℝ → ℝ),
 (∀ i j,Integrable (fun y => f i y*g j y) μ) → ∀ E : Set ℝ,MeasurableSet E → ∀ k : ℕ,k≤n →
 ((rowAffinePolynomialMatrix (Matrix.of (fun i j => ∫ y in E,f i y*g j y ∂μ))
 (Matrix.of (fun i j => ∫ y in Eᶜ,f i y*g j y ∂μ))).det).coeff k=
 (1/(n.factorial : ℝ))*countDeterminantMoment f g μ E k
def Mix : Prop := ∀ (n : ℕ) (μ : Measure ℝ) [SigmaFinite μ] (f g : Fin n → ℝ → ℝ),
 (∀ i j,Integrable (fun y => f i y*g j y) μ) → ∀ E : Set ℝ,MeasurableSet E → ∀ k : ℕ,k≤n →
 (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,if S.card=k then
 (rowMix (Matrix.of (fun i j => ∫ y in E,f i y*g j y ∂μ))
 (Matrix.of (fun i j => ∫ y in Eᶜ,f i y*g j y ∂μ)) S).det else 0)=
 (1/(n.factorial : ℝ))*countDeterminantMoment f g μ E k
end
end SheafSplitCount
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.split_andreief_count_generating,`SheafSplitCount.Generate),
 (`JinWishart.measurable_coordinateMembershipCount,`SheafSplitCount.Meas),
 (`JinWishart.andreief_det_product_integrable,`SheafSplitCount.Int),
 (`JinWishart.split_andreief_count_polynomial,`SheafSplitCount.Poly),
 (`JinWishart.split_andreief_count_coefficient,`SheafSplitCount.Coeff),
 (`JinWishart.split_andreief_count_rowMix,`SheafSplitCount.Mix)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Split count literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
