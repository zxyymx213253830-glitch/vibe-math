import JinWishartFormalization.ScaledMixedKernelMoments
import Lean
open MeasureTheory Set JinWishart
namespace SheafScaledMixedKernel
noncomputable section
def Scale : Prop := ∀ (q : ℕ) (lambda t c : ℝ), 0 < c →
 scalarSeriesKernel q (lambda/c) (c*t) = scalarSeriesKernel q lambda t
def Gamma : Prop := ∀ (k : ℕ) (c : ℝ), 0 < c →
 (∫ t in Ioi (0 : ℝ), t^k * Real.exp (-(c*t))) = (k.factorial : ℝ)/c^(k+1)
def KernelMoment : Prop := ∀ (q k : ℕ) (lambda c : ℝ), 0 ≤ lambda → 0 < c →
 (∫ t in Ioi (0 : ℝ), t^(q+k)*Real.exp (-(c*t))*scalarSeriesKernel q lambda t) =
 (Real.exp (lambda/c)*poissonFactorialMomentPolynomial q k (lambda/c))/c^(q+k+1)
end
end SheafScaledMixedKernel
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.scalarSeriesKernel_scale,`SheafScaledMixedKernel.Scale),
 (`JinWishart.integral_natPower_exp_neg_scaled,`SheafScaledMixedKernel.Gamma),
 (`JinWishart.scalarSeriesKernel_scaledMoment,`SheafScaledMixedKernel.KernelMoment)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Scaled mixed kernel literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
