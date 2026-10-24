import JinWishartFormalization.ActualCentralTwoByTwoJointDensity
import Lean
open MeasureTheory ProbabilityTheory Set JinWishart
open scoped ENNReal
namespace SheafActualTwoJoint
noncomputable section
def IntegralTarget : Prop := ∀ (F : ℝ × ℝ → ℝ≥0∞),Measurable F →
 (∫⁻ z : ComplexSample (m := 2) (n := 2), F (twoRowTraceRadius (twoRowTraceCoordinates
 (twoRowGramRealCoordinates (complexGram (complexSampleMatrix z))))) ∂stdGaussian _) =
 ∫⁻ t : ℝ, ∫⁻ r in Ioi (0 : ℝ),
 if r<t then ENNReal.ofReal (8*r^2*Real.exp (-2*t))*F (t,r) else 0
def DetTarget : Prop := traceRadiusEigenEquiv.toLinearMap.det=(-2 : ℝ)
def VolumeTarget : Prop := (volume : Measure (ℝ × ℝ)).map traceRadiusEigenEquiv=(1/2 : ℝ≥0∞) • volume
def TransportTarget : Prop := ∀ (f : ℝ × ℝ → ℝ≥0∞),Measurable f →
 ((volume : Measure (ℝ × ℝ)).withDensity f).map traceRadiusEigenCoordinates =
 volume.withDensity (fun y => (1/2 : ℝ≥0∞)*f (traceRadiusEigenInverse y))
def CandidateTarget : Prop :=
 (((volume : Measure (ℝ × ℝ)).restrict {x | 0<x.2 ∧ x.2<x.1}).withDensity
 (fun x => ENNReal.ofReal (8*x.2^2*Real.exp (-2*x.1)))).map traceRadiusEigenCoordinates =
 volume.withDensity centralTwoByTwoPaperEigenvalueDensity
def RadiusLawTarget : Prop := (stdGaussian (ComplexSample (m := 2) (n := 2))).map actualTwoRowTraceRadius =
 ((volume : Measure (ℝ × ℝ)).restrict {x | 0<x.2 ∧ x.2<x.1}).withDensity
 (fun x => ENNReal.ofReal (8*x.2^2*Real.exp (-2*x.1)))
def JointTarget : Prop := centralTwoByTwoJointEigenvalueLaw =
 (volume : Measure (ℝ × ℝ)).withDensity (fun y => if 0<y.2 ∧ y.2<y.1 then
 ENNReal.ofReal (Real.exp (-(y.1+y.2))*(y.1-y.2)^2) else 0)
def T3Target : Prop := ∀ (x : ℝ), centralTwoByTwoT3Increment x =
 ∫⁻ y in centralTwoByTwoT3Region x,centralTwoByTwoPaperEigenvalueDensity y ∂(volume : Measure (ℝ × ℝ))
end
end SheafActualTwoJoint
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
  (`JinWishart.actualTwoRow_traceRadius_lintegral,`SheafActualTwoJoint.IntegralTarget),
  (`JinWishart.traceRadiusEigenEquiv_det,`SheafActualTwoJoint.DetTarget),
  (`JinWishart.map_volume_traceRadiusEigenEquiv,`SheafActualTwoJoint.VolumeTarget),
  (`JinWishart.traceRadiusEigen_density_transport,`SheafActualTwoJoint.TransportTarget),
  (`JinWishart.traceRadiusDensity_spectral_transport,`SheafActualTwoJoint.CandidateTarget),
  (`JinWishart.actualTwoRow_traceRadius_eq_density,`SheafActualTwoJoint.RadiusLawTarget),
  (`JinWishart.actualCentralTwoByTwo_jointEigenvalueDensity,`SheafActualTwoJoint.JointTarget),
  (`JinWishart.actualCentralTwoByTwo_T3Increment_densityIntegral,`SheafActualTwoJoint.T3Target)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels name)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq actualType expectedType do throwError "Actual two-joint literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
