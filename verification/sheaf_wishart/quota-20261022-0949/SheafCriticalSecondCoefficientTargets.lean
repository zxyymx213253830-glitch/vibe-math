import JinWishartFormalization.ActualCriticalSecondCoefficient
import Lean
open Matrix JinWishart Module MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace SheafCriticalSecondCoefficient
noncomputable section
def FatouTarget : Prop := ∀ {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (μ : Measure Ω) (x : ι → Ω → ℝ)
    (hm : ∀ i,Measurable (x i)) (hx : ∀ i,∀ᵐ z ∂μ,0≤x i z)
    (hInv : (∫⁻ z,ENNReal.ofReal ((∑ i,((x i z)⁻¹)^2)/2) ∂μ)=⊤),
    Tendsto (fun t : ℝ => ∫⁻ z,ENNReal.ofReal
      (∑ i,t*((x i z)⁻¹-t*positiveModeOffsetError (x i z) t)) ∂μ) atTop (𝓝 ⊤)
def ActualTarget : Prop := ∀ {m p n r : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (hr : r=(Matrix.fromRows B M).rank) (hR : 0<min m r)
    (hb : 0<B.rank) (hcm : r-B.rank<m) (hk : max m r-min m r+1=2)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=min m r),
    let S := fun z : ComplexSample (m := m) (n := p) =>
      ∑ j,positiveSpectrumLog (actualCorrelatedEigenvalue B M j z)
    let L := fun z : ComplexSample (m := m) (n := p) =>
      ∑ j,(actualCorrelatedEigenvalue B M j z)⁻¹
    Integrable L (stdGaussian _) ∧
      Tendsto (fun t : ℝ => t*((∫ z,L z ∂stdGaussian _)-
        t*((∫ z,actualCorrelatedMatrixLogDet B M t z ∂stdGaussian _)-
          (min m r : ℕ)*Real.log t-(∫ z,S z ∂stdGaussian _)))) atTop atTop
end
end SheafCriticalSecondCoefficient
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [(`JinWishart.positiveSpectrum_second_gap_lintegral_tendsto_top,
   `SheafCriticalSecondCoefficient.FatouTarget),
   (`JinWishart.actualCorrelatedMatrixLogDet_critical_second_gap_tendsto_atTop,
   `SheafCriticalSecondCoefficient.ActualTarget)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels name)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF critical second-coefficient target differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
