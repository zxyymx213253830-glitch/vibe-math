import JinWishartFormalization.ActualSingularInverseClassification
import Lean
open Matrix JinWishart Module MeasureTheory ProbabilityTheory
namespace SheafSingularInverseClassification
noncomputable section
def CriterionTarget : Prop := ∀ {m p n r : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (hr : r=(Matrix.fromRows B M).rank) (hR : 0<min m r)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=min m r) (q : ℝ) (hq : 0<q),
    Integrable (fun z => (actualCorrelatedEigenvalue B M i z)⁻¹^q)
      (stdGaussian (ComplexSample (m := m) (n := p))) ↔
      B.rank=0 ∨ r-B.rank=m ∨ q<((max m r-min m r+1 : ℕ) : ℝ)
def DivergenceTarget : Prop := ∀ {m p n r : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (hr : r=(Matrix.fromRows B M).rank) (hR : 0<min m r) (hb : 0<B.rank)
    (hcm : r-B.rank<m) (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=min m r)
    (q : ℝ) (hq : ((max m r-min m r+1 : ℕ) : ℝ)≤q),
    (∫⁻ z : ComplexSample (m := m) (n := p),
      ENNReal.ofReal ((actualCorrelatedEigenvalue B M i z)⁻¹^q) ∂stdGaussian _)=⊤
def NoSpectrumTarget : Prop := ∀ {m p n r : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (hr : r=(Matrix.fromRows B M).rank) (hR : min m r=0),
    ∀ᵐ z ∂stdGaussian (ComplexSample (m := m) (n := p)),
      ∀ i : Fin (Fintype.card (Fin n)),¬0<actualCorrelatedEigenvalue B M i z
end
end SheafSingularInverseClassification
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [(`JinWishart.actual_singular_positive_inverse_realMoment_integrable_iff,
   `SheafSingularInverseClassification.CriterionTarget),
   (`JinWishart.actual_singular_positive_inverse_realMoment_lintegral_eq_top,
   `SheafSingularInverseClassification.DivergenceTarget),
   (`JinWishart.actual_singular_no_positive_spectrum_ae_of_generic_rank_zero,
   `SheafSingularInverseClassification.NoSpectrumTarget)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels name)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF singular classification target differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
