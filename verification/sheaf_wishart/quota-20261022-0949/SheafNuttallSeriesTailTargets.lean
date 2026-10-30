import JinWishartFormalization.NuttallSeriesTailBridge
import Lean
open MeasureTheory Set JinWishart
namespace SheafNuttallSeriesTail
noncomputable section
def Pointwise : Prop := ∀ (q k : ℕ) (lambda r : ℝ), 0 ≤ lambda → 0 ≤ r →
 (nuttallQIntegrand (q+2*k+1) q (Real.sqrt (2*lambda)) r).re =
 ((Real.sqrt 2)^q * 2^k) * (Real.sqrt lambda)^q * Real.exp (-lambda) *
 (r*((r^2/2)^(q+k)*Real.exp (-(r^2/2))*scalarSeriesKernel q lambda (r^2/2)))
def TailRe : Prop := ∀ (q k : ℕ) (lambda x : ℝ), 0 ≤ lambda → 0 ≤ x →
 (nuttallQ (q+2*k+1) q (Real.sqrt (2*lambda)) (Real.sqrt (2*x))).re =
 ((Real.sqrt 2)^q * 2^k) * (Real.sqrt lambda)^q * Real.exp (-lambda) *
 (∫ y in Ioi x, y^(q+k)*Real.exp (-y)*scalarSeriesKernel q lambda y)
def ScaledRe : Prop := ∀ (q k : ℕ) (lambda x : ℝ), 0 ≤ lambda → 0 ≤ x →
 Real.rpow 2 (-((q : ℝ)/2)-(k : ℝ)) *
 (nuttallQ (q+2*k+1) q (Real.sqrt (2*lambda)) (Real.sqrt (2*x))).re =
 (Real.sqrt lambda)^q * Real.exp (-lambda) *
 (∫ y in Ioi x, y^(q+k)*Real.exp (-y)*scalarSeriesKernel q lambda y)
def ImagZero : Prop := ∀ (q k : ℕ) (a b : ℝ), 0 ≤ b →
 (nuttallQ (q+2*k+1) q a b).im = 0
def ScaledComplex : Prop := ∀ (q k : ℕ) (lambda x : ℝ), 0 ≤ lambda → 0 ≤ x →
 (Real.rpow 2 (-((q : ℝ)/2)-(k : ℝ)) : ℂ) *
 nuttallQ (q+2*k+1) q (Real.sqrt (2*lambda)) (Real.sqrt (2*x)) =
 ((Real.sqrt lambda)^q * Real.exp (-lambda) *
 (∫ y in Ioi x, y^(q+k)*Real.exp (-y)*scalarSeriesKernel q lambda y) : ℝ)
end
end SheafNuttallSeriesTail
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.nuttall_series_integrand_re,`SheafNuttallSeriesTail.Pointwise),
 (`JinWishart.nuttallQ_series_tail_re,`SheafNuttallSeriesTail.TailRe),
 (`JinWishart.paperScaled_nuttallQ_series_tail_re,`SheafNuttallSeriesTail.ScaledRe),
 (`JinWishart.nuttallQ_natural_tail_im_zero,`SheafNuttallSeriesTail.ImagZero),
 (`JinWishart.paperScaled_nuttallQ_series_tail,`SheafNuttallSeriesTail.ScaledComplex)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Nuttall series tail literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
