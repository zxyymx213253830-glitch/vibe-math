import JinWishartFormalization.ActualCompressedInverseCriterion
import Lean
open Matrix JinWishart Module MeasureTheory ProbabilityTheory
namespace SheafCompressedInverse
noncomputable section
def CriterionTarget : Prop := ∀ {m p n r : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (hr : r=(Matrix.fromRows B M).rank) (hb : 0<B.rank)
    (hc : 0<r-B.rank) (hcm : r-B.rank<m)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=min m r)
    (q : ℝ) (hq : 0<q),
    Integrable (fun z => (actualCorrelatedEigenvalue B M i z)⁻¹^q)
      (stdGaussian (ComplexSample (m := m) (n := p))) ↔
      q<((max m r-min m r+1 : ℕ) : ℝ)
def DivergenceTarget : Prop := ∀ {m p n r : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (hr : r=(Matrix.fromRows B M).rank) (hb : 0<B.rank)
    (hc : 0<r-B.rank) (hcm : r-B.rank<m)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=min m r)
    (q : ℝ) (hq : ((max m r-min m r+1 : ℕ) : ℝ)≤q),
    (∫⁻ z : ComplexSample (m := m) (n := p),
      ENNReal.ofReal ((actualCorrelatedEigenvalue B M i z)⁻¹^q) ∂stdGaussian _)=⊤
end
end SheafCompressedInverse
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [(`JinWishart.actual_compressed_inverse_realMoment_integrable_iff,
   `SheafCompressedInverse.CriterionTarget),
   (`JinWishart.actual_compressed_inverse_realMoment_lintegral_eq_top,
   `SheafCompressedInverse.DivergenceTarget)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels name)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF compressed inverse target differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
