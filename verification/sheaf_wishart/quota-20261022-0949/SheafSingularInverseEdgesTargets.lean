import JinWishartFormalization.ActualSingularInverseEdges
import Lean
open Matrix JinWishart Module MeasureTheory ProbabilityTheory
namespace SheafSingularInverseEdges
noncomputable section
def ZeroNoiseTarget : Prop := ∀ {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (hB : B.rank=0) (i : Fin (Fintype.card (Fin n))) (q : ℝ),
    Integrable (fun z => (actualCorrelatedEigenvalue B M i z)⁻¹^q)
      (stdGaussian (ComplexSample (m := m) (n := p)))
def FullImageTarget : Prop := ∀ {m p n r : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (hr : r=(Matrix.fromRows B M).rank) (hm : 0<m) (hc : r-B.rank=m)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=min m r)
    (q : ℝ) (hq : 0≤q),
    Integrable (fun z => (actualCorrelatedEigenvalue B M i z)⁻¹^q)
      (stdGaussian (ComplexSample (m := m) (n := p)))
end
end SheafSingularInverseEdges
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [(`JinWishart.actual_inverse_realMoment_integrable_of_noise_rank_zero,
   `SheafSingularInverseEdges.ZeroNoiseTarget),
   (`JinWishart.actual_positive_boundary_inverse_integrable_of_noiseless_full_image,
   `SheafSingularInverseEdges.FullImageTarget)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels name)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF singular edge target differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
