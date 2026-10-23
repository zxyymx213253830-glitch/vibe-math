import JinWishartFormalization.ActualPositiveSecondCoefficient
import Lean
open Matrix JinWishart Module MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace SheafPositiveSecondCoefficient
noncomputable section
def ScalarTarget : Prop := ∀ (x : ℝ) (hx : 0≤x),
    Tendsto (fun t : ℝ => t*(x⁻¹-t*positiveModeOffsetError x t)) atTop (𝓝 ((x⁻¹)^2/2))
def ActualTarget : Prop := ∀ {m p n r : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (hr : r=(Matrix.fromRows B M).rank) (hR : 0<min m r)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=min m r)
    (hMoment : B.rank=0 ∨ r-B.rank=m ∨ (2 : ℝ)<((max m r-min m r+1 : ℕ) : ℝ)),
    let R : ℝ := (min m r : ℕ)
    let S := fun z : ComplexSample (m := m) (n := p) =>
      ∑ j,positiveSpectrumLog (actualCorrelatedEigenvalue B M j z)
    let L := fun z : ComplexSample (m := m) (n := p) => ∑ j,(actualCorrelatedEigenvalue B M j z)⁻¹
    let Q := fun z : ComplexSample (m := m) (n := p) => ∑ j,((actualCorrelatedEigenvalue B M j z)⁻¹)^2
    Integrable Q (stdGaussian _) ∧
      Tendsto (fun t : ℝ => t*((∫ z,L z ∂stdGaussian _)-
        t*((∫ z,actualCorrelatedMatrixLogDet B M t z ∂stdGaussian _)-R*Real.log t-
          (∫ z,S z ∂stdGaussian _)))) atTop (𝓝 ((∫ z,Q z ∂stdGaussian _)/2))
end
end SheafPositiveSecondCoefficient
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [(`JinWishart.positiveModeOffsetError_second_scaled_tendsto,
   `SheafPositiveSecondCoefficient.ScalarTarget),
   (`JinWishart.actualCorrelatedMatrixLogDet_expected_positive_second_coefficient,
   `SheafPositiveSecondCoefficient.ActualTarget)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels name)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF positive second-coefficient target differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
