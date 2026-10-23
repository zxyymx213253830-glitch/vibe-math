import JinWishartFormalization.ActualCriticalFirstCoefficient
import Lean
open Matrix JinWishart Module MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace SheafCriticalFirstCoefficient
noncomputable section
def FatouTarget : Prop := ∀ {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (μ : Measure Ω) (x : ι → Ω → ℝ)
    (hm : ∀ i,Measurable (x i)) (hx : ∀ i,∀ᵐ z ∂μ,0≤x i z)
    (hInv : (∫⁻ z,ENNReal.ofReal (∑ i,(x i z)⁻¹) ∂μ)=⊤),
    Tendsto (fun t : ℝ => ∫⁻ z,ENNReal.ofReal (t*(∑ i,positiveModeOffsetError (x i z) t)) ∂μ)
      atTop (𝓝 ⊤)
def ActualTarget : Prop := ∀ {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (hr : m=(Matrix.fromRows B M).rank) (hm : 0<m) (hb : 0<B.rank)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=m),
    let S := fun z : ComplexSample (m := m) (n := p) =>
      ∑ j,positiveSpectrumLog (actualCorrelatedEigenvalue B M j z)
    Tendsto (fun t : ℝ => t*((∫ z,actualCorrelatedMatrixLogDet B M t z ∂stdGaussian _)-
      (m : ℝ)*Real.log t-(∫ z,S z ∂stdGaussian _))) atTop atTop
end
end SheafCriticalFirstCoefficient
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [(`JinWishart.positiveSpectrum_scaled_offset_lintegral_tendsto_top,
   `SheafCriticalFirstCoefficient.FatouTarget),
   (`JinWishart.actualCorrelatedMatrixLogDet_critical_scaled_offset_tendsto_atTop,
   `SheafCriticalFirstCoefficient.ActualTarget)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels name)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF critical first-coefficient target differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
