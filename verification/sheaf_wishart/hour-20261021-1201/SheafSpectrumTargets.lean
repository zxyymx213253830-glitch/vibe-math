import JinWishartFormalization.PositiveSpectrumLogIntegrability
import Lean
open Matrix MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace SheafSpectrum
noncomputable section
def Upper : Prop := ∀ {x : ℝ}, 0≤x → JinWishart.positiveSpectrumLog x≤x
def Dom : Prop := ∀ {ι : Type} [Fintype ι] (f : ι→ℝ), (∀ i,0≤f i) → ∀ i,
 |JinWishart.positiveSpectrumLog (f i)| ≤ (∑ j,f j)+|∑ j,JinWishart.positiveSpectrumLog (f j)|
def Mode : Prop := ∀ {α ι : Type} [MeasurableSpace α] [Fintype ι] (μ : Measure α)
 (f : ι→α→ℝ), (∀ i,Measurable (f i)) → (∀ i,Integrable (f i) μ) →
 (∀ i,∀ᵐ a ∂μ,0≤f i a) → Integrable (fun a => ∑ i,JinWishart.positiveSpectrumLog (f i a)) μ →
 ∀ i,Integrable (fun a => JinWishart.positiveSpectrumLog (f i a)) μ
def Offset : Prop := ∀ {m p n : ℕ} (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ),
 Integrable (fun z => ∑ i,JinWishart.positiveSpectrumLog (JinWishart.actualCorrelatedEigenvalue B M i z))
  (stdGaussian (JinWishart.ComplexSample (m:=m) (n:=p))) →
 Tendsto (fun r : ℝ => (∫ z,JinWishart.actualCorrelatedMatrixLogDet B M r z ∂stdGaussian _)-
  ((min m (Matrix.fromRows B M).rank):ℝ)*Real.log r) atTop
  (𝓝 (∫ z,(∑ i,JinWishart.positiveSpectrumLog (JinWishart.actualCorrelatedEigenvalue B M i z)) ∂stdGaussian _))
end
end SheafSpectrum
open Lean Meta in
#eval show MetaM Unit from do
 for (target,expected) in [
  (`JinWishart.positiveSpectrumLog_le_self,`SheafSpectrum.Upper),
  (`JinWishart.abs_positiveSpectrumLog_le_trace_add_abs_sum,`SheafSpectrum.Dom),
  (`JinWishart.integrable_positiveSpectrumLog_of_sum,`SheafSpectrum.Mode),
  (`JinWishart.actualCorrelatedMatrixLogDet_offset_of_sum_log,`SheafSpectrum.Offset)] do
   let actualType ← inferType (← mkConstWithFreshMVarLevels target)
   let expectedType ← whnf (← mkConstWithFreshMVarLevels expected)
   unless ← isDefEq actualType expectedType do
    throwError "SHEAF target type differs: {target}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
