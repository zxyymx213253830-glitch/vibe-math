import JinWishartFormalization.CentralTwoColumnJointDensity
import Lean
open Matrix MeasureTheory ProbabilityTheory JinWishart
open scoped ComplexOrder
namespace SheafTwoColumnDensity
noncomputable section
def Meas : Prop := Measurable twoColumnMatrixEigenpair
def Product : Prop := ∀ A : Matrix (Fin 2) (Fin 2) ℂ,A.PosSemidef →
 ‖A.det‖=(twoColumnMatrixEigenpair A).1*(twoColumnMatrixEigenpair A).2
def Ordered : Prop := ∀ (m : ℕ) (z : ComplexSample (m := m) (n := 2)),centralTwoColumnEigenpair z=
 (complexNoncentralSampleEigenvalue (0 : Matrix (Fin m) (Fin 2) ℂ) 0 z,
 complexNoncentralSampleSmallestEigenvalue (0 : Matrix (Fin m) (Fin 2) ℂ) (by norm_num) z)
def Bias : Prop := ∀ d : ℕ,
 centralTwoByTwoJointEigenvalueLaw.withDensity (fun y => ENNReal.ofReal ((y.1*y.2)^d))=
 ENNReal.ofReal ((d.factorial : ℝ)*((d+1).factorial : ℝ)) • centralTwoColumnJointEigenvalueLaw d
def Density : Prop := ∀ d : ℕ,
 centralTwoColumnJointEigenvalueLaw d=(volume : Measure (ℝ × ℝ)).withDensity
 (fun y => if 0<y.2 ∧ y.2<y.1 then ENNReal.ofReal
  (Real.exp (-(y.1+y.2))*(y.1-y.2)^2*(y.1*y.2)^d/((d.factorial : ℝ)*((d+1).factorial : ℝ))) else 0)
end
end SheafTwoColumnDensity
open Lean Meta in
#eval show MetaM Unit from do
 for (name,target) in [
 (`JinWishart.measurable_twoColumnMatrixEigenpair,`SheafTwoColumnDensity.Meas),
 (`JinWishart.twoColumnMatrixEigenpair_det_product,`SheafTwoColumnDensity.Product),
 (`JinWishart.centralTwoColumnEigenpair_eq_ordered,`SheafTwoColumnDensity.Ordered),
 (`JinWishart.centralTwoColumn_joint_spectral_bias,`SheafTwoColumnDensity.Bias),
 (`JinWishart.actualCentralTwoColumn_jointEigenvalueDensity,`SheafTwoColumnDensity.Density)] do
  let a ← inferType (← mkConstWithFreshMVarLevels name)
  let e ← whnf (← mkConstWithFreshMVarLevels target)
  unless ← isDefEq a e do throwError "Two column joint density literal type differs: {name}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
