import JinWishartFormalization.RectangularFactorInverseCriterion
import Lean
open Matrix JinWishart Module MeasureTheory ProbabilityTheory
namespace SheafRectangularFactorInverse
noncomputable section
def FrameTarget : Prop := ∀ {p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (hB : B.rank=n),
    ∃ (S : Matrix (Fin n) (Fin n) ℂ) (U : Matrix (Fin p) (Fin n) ℂ),
      IsUnit S.det ∧ Uᴴ*U=1 ∧ B*S=U
def CriterionTarget : Prop := ∀ {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (hB : B.rank=n) (hm : 0<m) (hn : 0<n)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=min m n) (q : ℝ) (hq : 0<q),
    Integrable (fun z => (actualCorrelatedEigenvalue B M i z)⁻¹^q)
      (stdGaussian (ComplexSample (m := m) (n := p))) ↔
      q<((max m n-min m n+1 : ℕ) : ℝ)
end
end SheafRectangularFactorInverse
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [(`JinWishart.exists_rectangular_full_column_frame,
   `SheafRectangularFactorInverse.FrameTarget),
   (`JinWishart.actual_rectangular_factor_inverse_realMoment_integrable_iff,
   `SheafRectangularFactorInverse.CriterionTarget)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels name)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF rectangular factor target differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
