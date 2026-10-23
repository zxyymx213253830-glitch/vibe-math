import JinWishartFormalization.OneColumnNuttallNormalization
import Lean
open Matrix JinWishart MeasureTheory Set
namespace SheafNaturalNuttall
noncomputable section
def SeriesTarget : Prop := ∀ (q : ℕ) (z : ℂ),
  modifiedBesselI q z=(z/2)^q*∑' n : ℕ,(z^2/4)^n/
    ((n.factorial : ℂ)*((n+q).factorial : ℂ))
def RealSeriesTarget : Prop := ∀ (q : ℕ) (x : ℝ),
  (((x/2)^q*∑' n : ℕ,(x^2/4)^n/
    ((n.factorial : ℝ)*((n+q).factorial : ℝ)) : ℝ) : ℂ)=modifiedBesselI q (x : ℂ)
def IntegrandTarget : Prop := ∀ (q : ℕ) (a r : ℝ),
  nuttallQIntegrand (q+1) q a r=(a : ℂ)^q*(noncentralChiEvenRadialKernel q a r : ℂ)
def MassTarget : Prop := ∀ (q : ℕ) (a : ℝ),
  (∫ r in Ioi (0 : ℝ),noncentralChiEvenRadialKernel q a r)=1
def IntegrableTarget : Prop := ∀ (q : ℕ) (a : ℝ),
  IntegrableOn (noncentralChiEvenRadialKernel q a) (Ioi 0)
def NormalizationTarget : Prop := ∀ (q : ℕ) (a : ℝ),
  nuttallQ (q+1) q a 0=(a : ℂ)^q
def T1Target : Prop := ∀ (t : ℕ) (ht : 1≤t) (lambda x : ℝ) (hl : 0<lambda),
  theorem1CdfCandidate 1 t 1 ht (by omega) (fun _ : Fin 1 => lambda) x=
    1-‖theorem1OneColumnNuttallQ t lambda x‖/(Real.sqrt (2*lambda))^(t-1)
def T2Target : Prop := ∀ (t : ℕ) (ht : 1≤t) (lambda x : ℝ) (hl : 0<lambda),
  theorem2CdfCandidate 1 t 1 ht (by omega) (fun _ : Fin 1 => lambda) x=
    ‖(Real.sqrt (2*lambda) : ℂ)^(t-1)-theorem1OneColumnNuttallQ t lambda x‖/
      (Real.sqrt (2*lambda))^(t-1)
end
end SheafNaturalNuttall
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
   (`JinWishart.modifiedBesselI_nat_eq_factorialSeries,`SheafNaturalNuttall.SeriesTarget),
   (`JinWishart.modifiedBesselI_nat_ofReal_eq_realSeries,`SheafNaturalNuttall.RealSeriesTarget),
   (`JinWishart.nuttallQIntegrand_eq_evenRadialKernel,`SheafNaturalNuttall.IntegrandTarget),
   (`JinWishart.noncentralChiEvenRadialKernel_integral_eq_one,`SheafNaturalNuttall.MassTarget),
   (`JinWishart.integrableOn_noncentralChiEvenRadialKernel,`SheafNaturalNuttall.IntegrableTarget),
   (`JinWishart.nuttallQ_succ_self_zero,`SheafNaturalNuttall.NormalizationTarget),
   (`JinWishart.theorem1OneColumnCandidate_eq_explicitNormalizedQ,`SheafNaturalNuttall.T1Target),
   (`JinWishart.theorem2OneColumnCandidate_eq_explicitNormalizedQ,`SheafNaturalNuttall.T2Target)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels name)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF natural Nuttall target differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
