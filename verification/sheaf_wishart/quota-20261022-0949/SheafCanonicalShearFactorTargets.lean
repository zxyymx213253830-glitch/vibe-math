import JinWishartFormalization.CanonicalShearFactorMoments
import Lean
open Matrix JinWishart MeasureTheory ProbabilityTheory
namespace SheafCanonicalShearFactor
noncomputable section
def MomentTarget : Prop := ∀ {c b : ℕ}
    (Q : Matrix (Fin c) (Fin c) ℂ) (M : Matrix (Fin c) (Fin b) ℂ)
    (q : ℝ) (hq : 0≤q),
    Integrable (fun z : ComplexSample (m := c) (n := b) =>
      (1+‖(Matrix.toEuclideanLin (Q*(complexSampleMatrix z+M))).toContinuousLinearMap‖)^q)
      (stdGaussian (ComplexSample (m := c) (n := b)))
end
end SheafCanonicalShearFactor
open Lean Meta in
#eval show MetaM Unit from do
 let actualType ← inferType (← mkConstWithFreshMVarLevels `JinWishart.integrable_actual_canonical_shear_factor)
 let expectedType ← whnf (← mkConstWithFreshMVarLevels `SheafCanonicalShearFactor.MomentTarget)
 unless ← isDefEq actualType expectedType do
  throwError "SHEAF actual shear factor moment target differs"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
