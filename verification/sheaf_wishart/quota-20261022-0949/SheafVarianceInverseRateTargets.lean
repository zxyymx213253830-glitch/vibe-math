import JinWishartFormalization.ActualSingularVarianceRate
import Lean
open Matrix JinWishart Module MeasureTheory ProbabilityTheory
namespace SheafVarianceInverseRate
noncomputable section
def GeneralTarget : Prop := ∀ {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (u v : α → ℝ)
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ),
    |variance u μ-variance v μ|≤(∫ a,(u a-v a)^2 ∂μ)+
      2*Real.sqrt (∫ a,(u a-v a)^2 ∂μ)*Real.sqrt (variance v μ)
def ActualTarget : Prop := ∀ {m p n r : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (hr : r=(Matrix.fromRows B M).rank) (hR : 0<min m r)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=min m r)
    (hMoment : B.rank=0 ∨ r-B.rank=m ∨ (2 : ℝ)<((max m r-min m r+1 : ℕ) : ℝ)),
    let S := fun z : ComplexSample (m := m) (n := p) =>
      ∑ j,positiveSpectrumLog (actualCorrelatedEigenvalue B M j z)
    let K : ℝ := ∫ z,((actualCorrelatedEigenvalue B M i z)⁻¹)^2 ∂stdGaussian _
    ∀ t : ℝ,1≤t →
      |variance (actualCorrelatedMatrixLogDet B M t) (stdGaussian _)-variance S (stdGaussian _)|
        ≤((n : ℝ)*t⁻¹)^2*K+2*((n : ℝ)*t⁻¹)*Real.sqrt K*Real.sqrt (variance S (stdGaussian _))
end
end SheafVarianceInverseRate
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [(`JinWishart.variance_difference_le_mean_square,
   `SheafVarianceInverseRate.GeneralTarget),
   (`JinWishart.actualCorrelatedMatrixLogDet_variance_inverse_bound,
   `SheafVarianceInverseRate.ActualTarget)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels name)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF variance inverse-rate target differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
