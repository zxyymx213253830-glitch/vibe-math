import JinWishartFormalization.ActualSingularOffsetRate
import Lean
open Matrix JinWishart Module MeasureTheory ProbabilityTheory
namespace SheafOffsetInverseRate
noncomputable section
def ModeTarget : Prop := ∀ (x r : ℝ) (hx : 0≤x) (hr : 0<r),
    0≤positiveModeOffsetError x r ∧ positiveModeOffsetError x r≤r⁻¹*x⁻¹
def SpectrumTarget : Prop := ∀ {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hx : ∀ i,0≤x i) (a r : ℝ) (ha : 0<a) (hr : 0<r)
    (hmin : ∀ i,0<x i → a≤x i),
    0≤(∑ i,positiveModeOffsetError (x i) r) ∧
      (∑ i,positiveModeOffsetError (x i) r)≤(Fintype.card ι : ℝ)*r⁻¹*a⁻¹
def ActualTarget : Prop := ∀ {m p n r : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (hr : r=(Matrix.fromRows B M).rank) (hR : 0<min m r)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=min m r)
    (hMoment : B.rank=0 ∨ r-B.rank=m ∨ (2 : ℝ)<((max m r-min m r+1 : ℕ) : ℝ)),
    let R : ℝ := (min m r : ℕ)
    let S := fun z : ComplexSample (m := m) (n := p) =>
      ∑ j,positiveSpectrumLog (actualCorrelatedEigenvalue B M j z)
    Integrable (fun z => ((actualCorrelatedEigenvalue B M i z)⁻¹)^2) (stdGaussian _) ∧
      ∀ t : ℝ,1≤t →
        (∫ z,(actualCorrelatedMatrixLogDet B M t z-R*Real.log t-S z)^2 ∂stdGaussian _)
          ≤((n : ℝ)*t⁻¹)^2*(∫ z,((actualCorrelatedEigenvalue B M i z)⁻¹)^2 ∂stdGaussian _)
end
end SheafOffsetInverseRate
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [(`JinWishart.positiveModeOffsetError_nonneg_le_inverse,
   `SheafOffsetInverseRate.ModeTarget),
   (`JinWishart.finiteSpectrumOffsetError_nonneg_le_min_inverse,
   `SheafOffsetInverseRate.SpectrumTarget),
   (`JinWishart.actualCorrelatedMatrixLogDet_offset_mean_square_inverse_bound,
   `SheafOffsetInverseRate.ActualTarget)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels name)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF offset inverse-rate target differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
