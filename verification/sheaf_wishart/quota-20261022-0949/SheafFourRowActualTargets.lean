import JinWishartFormalization.Theorem12FourRowsActualCDF
import Lean
open Matrix JinWishart MeasureTheory ProbabilityTheory Set
namespace SheafFourRowActual
noncomputable section
def TailTarget : Prop := ∀ (q : ℕ) (a b : ℝ) (ha : 0<a) (hb : 0≤b),
  let L := ∫ r in Ioc (0 : ℝ) b,noncentralChiEvenRadialKernel q a r
  ‖nuttallQ (q+1) q a b‖=a^q*(1-L) ∧
    ‖(a : ℂ)^q-nuttallQ (q+1) q a b‖=a^q*L
def RadialTarget : Prop := ∀ (t : ℕ) (ht : 1≤t) (lambda x : ℝ) (hl : 0<lambda) (hx : 0≤x),
  let L := ∫ r in Ioc (0 : ℝ) (Real.sqrt (2*x)),
    noncentralChiEvenRadialKernel (t-1) (Real.sqrt (2*lambda)) r
  theorem1CdfCandidate 1 t 1 ht (by omega) (fun _ : Fin 1 => lambda) x=L ∧
    theorem2CdfCandidate 1 t 1 ht (by omega) (fun _ : Fin 1 => lambda) x=L
def ActualTarget : Prop := ∀ (M : Matrix (Fin 4) (Fin 1) ℂ) (x : ℝ)
  (hEnergy : 0<∑ i : Fin 4,‖M i 0‖^2) (hx : 0≤x),
  let lambda := ∑ i : Fin 4,‖M i 0‖^2
  let F := cdf ((stdGaussian (ComplexSample (m := 4) (n := 1))).map
    (complexNoncentralSampleSmallestEigenvalue M (by norm_num))) x
  theorem1CdfCandidate 1 4 1 (by omega) (by omega) (fun _ : Fin 1 => lambda) x=F ∧
    theorem2CdfCandidate 1 4 1 (by omega) (by omega) (fun _ : Fin 1 => lambda) x=F
end
end SheafFourRowActual
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
   (`JinWishart.nuttallQ_succ_self_tail_norms,`SheafFourRowActual.TailTarget),
   (`JinWishart.theorem12OneColumnCandidates_eq_radialCDF,`SheafFourRowActual.RadialTarget),
   (`JinWishart.theorem12FourRowsCandidates_eq_actualCDF_frobenius,`SheafFourRowActual.ActualTarget)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels name)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF four-row actual target differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
