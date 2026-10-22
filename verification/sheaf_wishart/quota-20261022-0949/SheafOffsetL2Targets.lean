import JinWishartFormalization.ActualSingularOffsetL2
import Lean
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace SheafOffsetL2
noncomputable section
def Bound : Prop := ∀ x r : ℝ,0≤x → 1≤r →
 0≤JinWishart.positiveModeOffsetError x r ∧ JinWishart.positiveModeOffsetError x r≤x+|JinWishart.positiveSpectrumLog x|
def Pointwise : Prop := ∀ x : ℝ,0≤x → Tendsto (JinWishart.positiveModeOffsetError x) atTop (𝓝 0)
def Finite : Prop := ∀ {α ι : Type*} [MeasurableSpace α] [Fintype ι] (μ : Measure α) (f : ι→α→ℝ),
 (∀ i,Measurable (f i)) → (∀ i,∀ᵐ a ∂μ,0≤f i a) →
 (∀ i,Integrable (fun a=>(f i a)^2) μ) → (∀ i,Integrable (fun a=>(JinWishart.positiveSpectrumLog (f i a))^2) μ) →
 (∀ r : ℝ,1≤r → Integrable (fun a=>(∑ i,JinWishart.positiveModeOffsetError (f i a) r)^2) μ) ∧
 Tendsto (fun r : ℝ=>∫ a,(∑ i,JinWishart.positiveModeOffsetError (f i a) r)^2 ∂μ) atTop (𝓝 0)
def Actual : Prop := ∀ {m p n : ℕ} (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ),
 let R : ℝ := (min m (Matrix.fromRows B M).rank : ℕ)
 let S := fun z : JinWishart.ComplexSample (m := m) (n := p)=>∑ i,JinWishart.positiveSpectrumLog (JinWishart.actualCorrelatedEigenvalue B M i z)
 (∀ r : ℝ,1≤r → Integrable (fun z=>(JinWishart.actualCorrelatedMatrixLogDet B M r z-R*Real.log r-S z)^2) (stdGaussian _)) ∧
 Tendsto (fun r : ℝ=>∫ z,(JinWishart.actualCorrelatedMatrixLogDet B M r z-R*Real.log r-S z)^2 ∂stdGaussian _) atTop (𝓝 0)
end
end SheafOffsetL2
open Lean Meta in
#eval show MetaM Unit from do
 for (target,expected) in [
 (`JinWishart.positiveModeOffsetError_nonneg_le,`SheafOffsetL2.Bound),
 (`JinWishart.positiveModeOffsetError_tendsto,`SheafOffsetL2.Pointwise),
 (`JinWishart.integral_finiteSpectrumOffsetError_sq_tendsto,`SheafOffsetL2.Finite),
 (`JinWishart.actualCorrelatedMatrixLogDet_offset_mean_square,`SheafOffsetL2.Actual)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels target)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels expected)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF target type differs: {target}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
