import JinWishartFormalization.GeneralOneColumnActualCDF
import Lean
open MeasureTheory ProbabilityTheory JinWishart Set
namespace SheafGeneralOneColumn
noncomputable section
def ProbabilityTarget : Prop := ∀ (q : ℕ) (a : ℝ), IsProbabilityMeasure (evenRadialMeasure q a)
def IntegralTarget : Prop := ∀ (q : ℕ) (a : ℝ) (f : ℝ → ℝ),
 (∫ r, f r ∂evenRadialMeasure q a)=∫ r in Ioi (0 : ℝ),noncentralChiEvenRadialKernel q a r*f r
def MGFTarget : Prop := ∀ (q : ℕ) (a t : ℝ), t<1 →
 mgf (fun r : ℝ => r^2/2) (evenRadialMeasure q a) t=Real.exp (a^2*t/(2*(1-t)))/(1-t)^(q+1)
def IntegrableTarget : Prop := ∀ (q : ℕ) (a t : ℝ), t<1 →
 Integrable (fun r : ℝ => Real.exp (t*(r^2/2))) (evenRadialMeasure q a)
def ProductLawTarget : Prop := ∀ {ι : Type} [Fintype ι] (q : ℕ),
 Fintype.card ι=2*(q+1) → ∀ (u : ι → ℝ) (a : ℝ), a^2=∑ i,(u i)^2 →
 (Measure.pi (fun _ : ι => gaussianReal 0 1)).map (fun x : ι → ℝ => (∑ i,(x i+u i)^2)/2)=
 (evenRadialMeasure q a).map (fun r : ℝ => r^2/2)
def EuclideanLawTarget : Prop := ∀ {ι : Type} [Fintype ι] (q : ℕ),
 Fintype.card ι=2*(q+1) → ∀ (u : EuclideanSpace ℝ ι),
 (stdGaussian (EuclideanSpace ℝ ι)).map (fun z => ‖z+u‖^2/2)=
 (evenRadialMeasure q ‖u‖).map (fun r : ℝ => r^2/2)
def RadialCDFTarget : Prop := ∀ (q : ℕ) (a x : ℝ), 0≤x →
 cdf ((evenRadialMeasure q a).map (fun r : ℝ => r^2/2)) x=
 ∫ r in Ioc (0 : ℝ) (Real.sqrt (2*x)),noncentralChiEvenRadialKernel q a r
def ActualCDFTarget : Prop := ∀ {m : ℕ}, 0<m → ∀ (M : Matrix (Fin m) (Fin 1) ℂ) (x : ℝ), 0≤x →
 cdf ((stdGaussian (ComplexSample (m := m) (n := 1))).map
 (complexNoncentralSampleSmallestEigenvalue M (by norm_num))) x=
 ∫ r in Ioc (0 : ℝ) (Real.sqrt (2*x)),noncentralChiEvenRadialKernel (m-1) ‖complexSampleMean M‖ r
def PaperTarget : Prop := ∀ {m : ℕ} (hm : 0<m) (M : Matrix (Fin m) (Fin 1) ℂ) (x : ℝ),
 0<∑ i : Fin m,‖M i 0‖^2 → 0≤x →
 let lambda := ∑ i : Fin m,‖M i 0‖^2
 let F := cdf ((stdGaussian (ComplexSample (m := m) (n := 1))).map
 (complexNoncentralSampleSmallestEigenvalue M (by norm_num))) x
 theorem1CdfCandidate 1 m 1 (by omega) (by omega) (fun _ : Fin 1 => lambda) x=F ∧
 theorem2CdfCandidate 1 m 1 (by omega) (by omega) (fun _ : Fin 1 => lambda) x=F
end
end SheafGeneralOneColumn
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
  (`JinWishart.evenRadialMeasure_isProbabilityMeasure,`SheafGeneralOneColumn.ProbabilityTarget),
  (`JinWishart.evenRadialMeasure_integral,`SheafGeneralOneColumn.IntegralTarget),
  (`JinWishart.evenRadialMeasure_mgf,`SheafGeneralOneColumn.MGFTarget),
  (`JinWishart.evenRadialMeasure_integrable_exp_energy,`SheafGeneralOneColumn.IntegrableTarget),
  (`JinWishart.gaussianPi_energy_eq_evenRadialLaw,`SheafGeneralOneColumn.ProductLawTarget),
  (`JinWishart.stdGaussian_energy_eq_evenRadialLaw,`SheafGeneralOneColumn.EuclideanLawTarget),
  (`JinWishart.evenRadialMeasure_energyCDF,`SheafGeneralOneColumn.RadialCDFTarget),
  (`JinWishart.noncentralColumnCDF_eq_generalRadialIntegral,`SheafGeneralOneColumn.ActualCDFTarget),
  (`JinWishart.theorem12OneColumnCandidates_eq_actualCDF_frobenius,`SheafGeneralOneColumn.PaperTarget)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels name)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF general one-column target differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
