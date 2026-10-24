import JinWishartFormalization.TwoByTwoTraceDensity
import Lean
open MeasureTheory ProbabilityTheory Set JinWishart
open scoped ENNReal
namespace SheafTwoTrace
noncomputable section
def DetTarget : Prop := twoRowTraceEquiv.toLinearMap.det=-(1/2 : ℝ)
def VolumeTarget : Prop := (volume : Measure GramChartSpace).map twoRowTraceEquiv=(2 : ℝ≥0∞) • volume
def ConeTarget : Prop := ∀ (q : GramChartSpace),
 (0<q 0 ∧ q 1^2+q 2^2<q 0*q 3) ↔
 (0<twoRowTraceCoordinates q 0 ∧ (twoRowTraceCoordinates q 1)^2+
 (twoRowTraceCoordinates q 2)^2+(twoRowTraceCoordinates q 3)^2<(twoRowTraceCoordinates q 0)^2)
def NormTarget : Prop := ∀ (p : GramChartSpace),
 (0<p 0 ∧ p 1^2+p 2^2+p 3^2<(p 0)^2) ↔
 ‖(WithLp.toLp 2 ![p 1,p 2,p 3] : EuclideanSpace ℝ (Fin 3))‖<p 0
def TransportTarget : Prop := ∀ (f : GramChartSpace → ℝ≥0∞),Measurable f →
 ((volume : Measure GramChartSpace).withDensity f).map twoRowTraceCoordinates=
 volume.withDensity (fun p => 2*f (twoRowTraceInverse p))
def ActualTarget : Prop := (stdGaussian (ComplexSample (m := 2) (n := 2))).map
 (fun z => twoRowTraceCoordinates (twoRowGramRealCoordinates (complexGram (complexSampleMatrix z))))=
 (volume.restrict {p : GramChartSpace | 0<p 0 ∧ p 1^2+p 2^2+p 3^2<(p 0)^2}).withDensity
 (fun p => ENNReal.ofReal (2*Real.pi⁻¹*Real.exp (-2*p 0)))
end
end SheafTwoTrace
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
  (`JinWishart.twoRowTraceEquiv_det,`SheafTwoTrace.DetTarget),
  (`JinWishart.map_volume_twoRowTraceEquiv,`SheafTwoTrace.VolumeTarget),
  (`JinWishart.twoRowTraceCoordinates_cone,`SheafTwoTrace.ConeTarget),
  (`JinWishart.twoRowTraceCone_iff_norm,`SheafTwoTrace.NormTarget),
  (`JinWishart.twoRowTrace_density_transport,`SheafTwoTrace.TransportTarget),
  (`JinWishart.actualTwoRow_traceCoordinates_eq_density,`SheafTwoTrace.ActualTarget)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels name)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF two-trace target differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
