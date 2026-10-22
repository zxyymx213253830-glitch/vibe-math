import JinWishartFormalization.ActualSingularLogDetVarianceLimit
import Lean
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace SheafVarianceLimit
noncomputable section
def Bound : Prop := ∀ {α : Type*} [MeasurableSpace α] (μ : Measure α) (u v : α→ℝ),
 MemLp u 2 μ → MemLp v 2 μ →
 |(∫ a,(u a)^2 ∂μ)-(∫ a,(v a)^2 ∂μ)|≤(∫ a,(u a-v a)^2 ∂μ)+
 2*Real.sqrt (∫ a,(u a-v a)^2 ∂μ)*Real.sqrt (∫ a,(v a)^2 ∂μ)
def Continuity : Prop := ∀ {α : Type*} [MeasurableSpace α] (μ : Measure α) (u : ℝ→α→ℝ) (v : α→ℝ),
 (∀ r : ℝ,1≤r → MemLp (u r) 2 μ) → MemLp v 2 μ →
 Tendsto (fun r : ℝ=>∫ a,(u r a-v a)^2 ∂μ) atTop (𝓝 0) →
 Tendsto (fun r : ℝ=>∫ a,(u r a)^2 ∂μ) atTop (𝓝 (∫ a,(v a)^2 ∂μ))
def Offset : Prop := ∀ {m p n : ℕ} (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ),
 let R : ℝ := (min m (Matrix.fromRows B M).rank : ℕ)
 let S := fun z : JinWishart.ComplexSample (m := m) (n := p)=>∑ i,JinWishart.positiveSpectrumLog (JinWishart.actualCorrelatedEigenvalue B M i z)
 (∀ r : ℝ,1≤r → MemLp (fun z=>JinWishart.actualCorrelatedMatrixLogDet B M r z-R*Real.log r) 2 (stdGaussian _)) ∧
 Tendsto (fun r : ℝ=>∫ z,(JinWishart.actualCorrelatedMatrixLogDet B M r z-R*Real.log r)^2 ∂stdGaussian _)
 atTop (𝓝 (∫ z,(S z)^2 ∂stdGaussian _))
def VarianceLimit : Prop := ∀ {m p n : ℕ} (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ),
 let S := fun z : JinWishart.ComplexSample (m := m) (n := p)=>∑ i,JinWishart.positiveSpectrumLog (JinWishart.actualCorrelatedEigenvalue B M i z)
 (∀ r : ℝ,1≤r → MemLp (JinWishart.actualCorrelatedMatrixLogDet B M r) 2 (stdGaussian _)) ∧
 Tendsto (fun r : ℝ=>ProbabilityTheory.variance (JinWishart.actualCorrelatedMatrixLogDet B M r) (stdGaussian _))
 atTop (𝓝 (ProbabilityTheory.variance S (stdGaussian _)))
end
end SheafVarianceLimit
open Lean Meta in
#eval show MetaM Unit from do
 for (target,expected) in [
 (`JinWishart.integral_square_difference_bound,`SheafVarianceLimit.Bound),
 (`JinWishart.integral_square_tendsto_of_mean_square,`SheafVarianceLimit.Continuity),
 (`JinWishart.actualCorrelatedMatrixLogDet_offset_second_moment,`SheafVarianceLimit.Offset),
 (`JinWishart.actualCorrelatedMatrixLogDet_variance_tendsto,`SheafVarianceLimit.VarianceLimit)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels target)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels expected)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF target type differs: {target}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
