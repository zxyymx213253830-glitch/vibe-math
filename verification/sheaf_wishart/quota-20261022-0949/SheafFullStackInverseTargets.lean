import JinWishartFormalization.ActualFullStackInverseCriterion
import Lean
open Matrix JinWishart Module MeasureTheory ProbabilityTheory
namespace SheafFullStackInverse
noncomputable section
def CriterionTarget : Prop := ∀ {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (hstack : (Matrix.fromRows B M).rank=n) (hb : 0<B.rank)
    (hc : 0<finrank ℂ B.toEuclideanLin.ker)
    (hcm : finrank ℂ B.toEuclideanLin.ker<m)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=min m n)
    (q : ℝ) (hq : 0<q),
    Integrable (fun z => (actualCorrelatedEigenvalue B M i z)⁻¹^q)
      (stdGaussian (ComplexSample (m := m) (n := p))) ↔
      q<((max m n-min m n+1 : ℕ) : ℝ)
def DivergenceTarget : Prop := ∀ {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (hstack : (Matrix.fromRows B M).rank=n) (hb : 0<B.rank)
    (hc : 0<finrank ℂ B.toEuclideanLin.ker)
    (hcm : finrank ℂ B.toEuclideanLin.ker<m)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=min m n)
    (q : ℝ) (hq : ((max m n-min m n+1 : ℕ) : ℝ)≤q),
    (∫⁻ z : ComplexSample (m := m) (n := p),
      ENNReal.ofReal ((actualCorrelatedEigenvalue B M i z)⁻¹^q) ∂stdGaussian _)=⊤
end
end SheafFullStackInverse
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [(`JinWishart.actual_full_stack_inverse_realMoment_integrable_iff,
   `SheafFullStackInverse.CriterionTarget),
   (`JinWishart.actual_full_stack_inverse_realMoment_lintegral_eq_top,
   `SheafFullStackInverse.DivergenceTarget)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels name)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF full-stack inverse target differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
