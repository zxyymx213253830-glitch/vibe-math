import JinWishartFormalization.ActualSingularFractionalRates
import Lean
open Matrix JinWishart Module MeasureTheory ProbabilityTheory
namespace SheafFractionalOffset
noncomputable section
def ModeTarget : Prop := ∀ (x t α : ℝ)
    (hx : 0≤x) (ht : 0<t) (ha : 0<α) (ha1 : α≤1),
    0≤positiveModeOffsetError x t ∧
      positiveModeOffsetError x t≤α⁻¹*(t⁻¹)^α*(x⁻¹)^α
def SpectrumTarget : Prop := ∀ {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (hx : ∀ i,0≤x i) (a t α : ℝ) (ha : 0<a) (ht : 0<t)
    (hα : 0<α) (hα1 : α≤1) (hmin : ∀ i,0<x i → a≤x i),
    0≤(∑ i,positiveModeOffsetError (x i) t) ∧
      (∑ i,positiveModeOffsetError (x i) t)≤
        (Fintype.card ι : ℝ)*α⁻¹*(t⁻¹)^α*(a⁻¹)^α
def MseTarget : Prop := ∀ {m p n r : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (hr : r=(Matrix.fromRows B M).rank) (hR : 0<min m r)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=min m r)
    (α : ℝ) (hα : 0<α) (hα1 : α≤1)
    (hMoment : B.rank=0 ∨ r-B.rank=m ∨ 2*α<((max m r-min m r+1 : ℕ) : ℝ)),
    let R : ℝ := (min m r : ℕ)
    let S := fun z : ComplexSample (m := m) (n := p) =>
      ∑ j,positiveSpectrumLog (actualCorrelatedEigenvalue B M j z)
    Integrable (fun z => ((actualCorrelatedEigenvalue B M i z)⁻¹)^(2*α)) (stdGaussian _) ∧
      ∀ t : ℝ,1≤t →
        (∫ z,(actualCorrelatedMatrixLogDet B M t z-R*Real.log t-S z)^2 ∂stdGaussian _)
          ≤((n : ℝ)*α⁻¹*(t⁻¹)^α)^2*
            (∫ z,((actualCorrelatedEigenvalue B M i z)⁻¹)^(2*α) ∂stdGaussian _)
def VarianceTarget : Prop := ∀ {m p n r : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (hr : r=(Matrix.fromRows B M).rank) (hR : 0<min m r)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=min m r)
    (α : ℝ) (hα : 0<α) (hα1 : α≤1)
    (hMoment : B.rank=0 ∨ r-B.rank=m ∨ 2*α<((max m r-min m r+1 : ℕ) : ℝ)),
    let S := fun z : ComplexSample (m := m) (n := p) =>
      ∑ j,positiveSpectrumLog (actualCorrelatedEigenvalue B M j z)
    let K : ℝ := ∫ z,((actualCorrelatedEigenvalue B M i z)⁻¹)^(2*α) ∂stdGaussian _
    ∀ t : ℝ,1≤t →
      |variance (actualCorrelatedMatrixLogDet B M t) (stdGaussian _)-variance S (stdGaussian _)|
        ≤((n : ℝ)*α⁻¹*(t⁻¹)^α)^2*K+
          2*((n : ℝ)*α⁻¹*(t⁻¹)^α)*Real.sqrt K*Real.sqrt (variance S (stdGaussian _))
end
end SheafFractionalOffset
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [(`JinWishart.positiveModeOffsetError_fractional_bound,
   `SheafFractionalOffset.ModeTarget),
   (`JinWishart.finiteSpectrumOffsetError_fractional_min_bound,
   `SheafFractionalOffset.SpectrumTarget),
   (`JinWishart.actualCorrelatedMatrixLogDet_offset_fractional_mean_square_bound,
   `SheafFractionalOffset.MseTarget),
   (`JinWishart.actualCorrelatedMatrixLogDet_variance_fractional_bound,
   `SheafFractionalOffset.VarianceTarget)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels name)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF fractional offset target differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
