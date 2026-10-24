import JinWishartFormalization.CentralTwoByTwoMaximumClosedCDF
import Lean
open MeasureTheory ProbabilityTheory Set JinWishart
open scoped ENNReal
namespace SheafActualTwoMaximum
noncomputable section
def HalfTarget : Prop := ∀ (μ : Measure ℝ) [SFinite μ] (H : ℝ × ℝ → ℝ≥0∞),Measurable H →
 (∀ x y,H (x,y)=H (y,x)) → (∀ x,H (x,x)=0) →
 (∫⁻ z in {z : ℝ × ℝ | z.2<z.1},H z ∂μ.prod μ)=(1/2 : ℝ≥0∞)*∫⁻ z,H z ∂μ.prod μ
def GapTarget : Prop := ∀ (μ : Measure ℝ) [IsFiniteMeasure μ],
 Integrable (fun y : ℝ => y) μ → Integrable (fun y : ℝ => y^2) μ →
 0≤twoMomentDeterminant μ ∧
 (∫⁻ z in {z : ℝ × ℝ | z.2<z.1},ENNReal.ofReal ((z.1-z.2)^2) ∂μ.prod μ)=ENNReal.ofReal (twoMomentDeterminant μ)
def FiniteTarget : Prop := ∀ (x : ℝ),IsFiniteMeasure (exponentialIntervalMeasure x)
def IntPowTarget : Prop := ∀ (x : ℝ) (k : ℕ),Integrable (fun y : ℝ => y^k) (exponentialIntervalMeasure x)
def GammaTarget : Prop := ∀ (k : ℕ) (x : ℝ),Complex.partialGamma ((k+1 : ℕ) : ℂ) x=
 ((∫ y in (0 : ℝ)..x,y^k*Real.exp (-y) : ℝ) : ℂ)
def MomentGammaTarget : Prop := ∀ (x : ℝ),0≤x → ∀ (k : ℕ),
 ((∫ y : ℝ,y^k ∂exponentialIntervalMeasure x : ℝ) : ℂ)=Complex.partialGamma ((k+1 : ℕ) : ℂ) x
def XiTarget : Prop := ∀ (x : ℝ),0≤x →
 (theorem2XiMatrix 2 2 0 (by omega) (by omega) (fun j : Fin 0 => Fin.elim0 j) x).det=
 (twoMomentDeterminant (exponentialIntervalMeasure x) : ℂ)
def ActualTarget : Prop := ∀ (x : ℝ),
 (stdGaussian (ComplexSample (m := 2) (n := 2))) {z | (centralTwoByTwoEigenpair z).1≤x}=
 ENNReal.ofReal (twoMomentDeterminant (exponentialIntervalMeasure x))
def PaperActualTarget : Prop := ∀ (x : ℝ),0≤x →
 theorem2CdfCandidate 2 2 0 (by omega) (by omega) (fun j : Fin 0 => Fin.elim0 j) x=
 ((stdGaussian (ComplexSample (m := 2) (n := 2))) {z | (centralTwoByTwoEigenpair z).1≤x}).toReal
def ClosedXiTarget : Prop := ∀ (x : ℝ),0≤x →
 (theorem2XiMatrix 2 2 0 (by omega) (by omega) (fun j : Fin 0 => Fin.elim0 j) x).det=
 ((1-(x^2+2)*Real.exp (-x)+Real.exp (-2*x) : ℝ) : ℂ)
def ClosedActualTarget : Prop := ∀ (x : ℝ),0≤x →
 ((stdGaussian (ComplexSample (m := 2) (n := 2))) {z | (centralTwoByTwoEigenpair z).1≤x}).toReal=
 1-(x^2+2)*Real.exp (-x)+Real.exp (-2*x)
def ClosedPaperTarget : Prop := ∀ (x : ℝ),0≤x →
 theorem2CdfCandidate 2 2 0 (by omega) (by omega) (fun j : Fin 0 => Fin.elim0 j) x=
 1-(x^2+2)*Real.exp (-x)+Real.exp (-2*x)
end
end SheafActualTwoMaximum
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
  (`JinWishart.lintegral_symmetric_ordered_half,`SheafActualTwoMaximum.HalfTarget),
  (`JinWishart.ordered_square_gap_moment_identity,`SheafActualTwoMaximum.GapTarget),
  (`JinWishart.exponentialIntervalMeasure_isFinite,`SheafActualTwoMaximum.FiniteTarget),
  (`JinWishart.exponentialInterval_integrable_pow,`SheafActualTwoMaximum.IntPowTarget),
  (`JinWishart.partialGamma_nat_succ_eq_realInterval,`SheafActualTwoMaximum.GammaTarget),
  (`JinWishart.exponentialInterval_integral_pow_eq_partialGamma,`SheafActualTwoMaximum.MomentGammaTarget),
  (`JinWishart.theorem2CentralTwoRow_XiDet_eq_intervalMoments,`SheafActualTwoMaximum.XiTarget),
  (`JinWishart.actualCentralTwoByTwo_maximumCDF_eq_momentDet,`SheafActualTwoMaximum.ActualTarget),
  (`JinWishart.theorem2CentralTwoRow_candidate_eq_actualCDF,`SheafActualTwoMaximum.PaperActualTarget),
  (`JinWishart.theorem2CentralTwoRow_XiDet_eq_closedCDF,`SheafActualTwoMaximum.ClosedXiTarget),
  (`JinWishart.actualCentralTwoByTwo_maximum_CDF,`SheafActualTwoMaximum.ClosedActualTarget),
  (`JinWishart.theorem2CentralTwoRow_candidate_eq_closedCDF,`SheafActualTwoMaximum.ClosedPaperTarget)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels name)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq actualType expectedType do throwError "Actual two-maximum literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
