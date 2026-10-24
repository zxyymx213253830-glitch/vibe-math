import JinWishartFormalization.GaussianFiniteSquareMGF
import JinWishartFormalization.EvenRadialWeightedIntegral
import Lean
open MeasureTheory ProbabilityTheory Set
namespace SheafFiniteRadialMGF
noncomputable section
def ProductIntegral : Prop := ∀ {ι : Type} [Fintype ι] (u : ι → ℝ) (t : ℝ), t<1 →
 (∫ x : ι → ℝ, Real.exp (t*(∑ i,(x i+u i)^2)/2) ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
 ((Real.sqrt (1-t))⁻¹)^Fintype.card ι * Real.exp ((∑ i,(u i)^2)*t/(2*(1-t)))
def ProductIntegrable : Prop := ∀ {ι : Type} [Fintype ι] (u : ι → ℝ) (t : ℝ), t<1 →
 Integrable (fun x : ι → ℝ => Real.exp (t*(∑ i,(x i+u i)^2)/2))
 (Measure.pi (fun _ : ι => gaussianReal 0 1))
def Scaling : Prop := ∀ (q : ℕ) (a r c : ℝ), 0<c →
 c^(2*q+1)*Real.exp ((1-c^2)*r^2/2)*JinWishart.noncentralChiEvenRadialKernel q a r =
 Real.exp (a^2*(1-c^2)/(2*c^2))*JinWishart.noncentralChiEvenRadialKernel q (a/c) (c*r)
def ScaleIntegral : Prop := ∀ (q : ℕ) (a c : ℝ), 0<c →
 (∫ r in Ioi (0 : ℝ), Real.exp ((1-c^2)*r^2/2)*JinWishart.noncentralChiEvenRadialKernel q a r) =
 Real.exp (a^2*(1-c^2)/(2*c^2))/c^(2*(q+1))
def ScaleIntegrable : Prop := ∀ (q : ℕ) (a c : ℝ), 0<c →
 IntegrableOn (fun r : ℝ => Real.exp ((1-c^2)*r^2/2)*JinWishart.noncentralChiEvenRadialKernel q a r) (Ioi 0)
def MGFIntegral : Prop := ∀ (q : ℕ) (a t : ℝ), t<1 →
 (∫ r in Ioi (0 : ℝ), Real.exp (t*r^2/2)*JinWishart.noncentralChiEvenRadialKernel q a r) =
 Real.exp (a^2*t/(2*(1-t)))/(1-t)^(q+1)
def MGFIntegrable : Prop := ∀ (q : ℕ) (a t : ℝ), t<1 →
 IntegrableOn (fun r : ℝ => Real.exp (t*r^2/2)*JinWishart.noncentralChiEvenRadialKernel q a r) (Ioi 0)
end
end SheafFiniteRadialMGF
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
  (`JinWishart.gaussianPi_integral_exp_shifted_square_sum,`SheafFiniteRadialMGF.ProductIntegral),
  (`JinWishart.gaussianPi_integrable_exp_shifted_square_sum,`SheafFiniteRadialMGF.ProductIntegrable),
  (`JinWishart.evenRadialKernel_scaling,`SheafFiniteRadialMGF.Scaling),
  (`JinWishart.evenRadialKernel_weighted_integral,`SheafFiniteRadialMGF.ScaleIntegral),
  (`JinWishart.evenRadialKernel_weighted_integrable,`SheafFiniteRadialMGF.ScaleIntegrable),
  (`JinWishart.evenRadialKernel_mgf_integral,`SheafFiniteRadialMGF.MGFIntegral),
  (`JinWishart.evenRadialKernel_mgf_integrable,`SheafFiniteRadialMGF.MGFIntegrable)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels name)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF finite/radial MGF target differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
