import JinWishartFormalization.ActualSingularPositiveLogSquare
import Lean
open Matrix MeasureTheory ProbabilityTheory
namespace SheafSingularLogSquare
noncomputable section
def SumSquare : Prop := ∀ {m p n : ℕ} (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ),
 Integrable (fun z=>(∑ i,JinWishart.positiveSpectrumLog (JinWishart.actualCorrelatedEigenvalue B M i z))^2)
 (stdGaussian (JinWishart.ComplexSample (m := m) (n := p)))
def ModeSquare : Prop := ∀ {m p n : ℕ} (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
 (i : Fin (Fintype.card (Fin n))),
 Integrable (fun z=>(JinWishart.positiveSpectrumLog (JinWishart.actualCorrelatedEigenvalue B M i z))^2)
 (stdGaussian (JinWishart.ComplexSample (m := m) (n := p)))
def Centered : Prop := ∀ {m p n : ℕ} (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ),
 let S := fun z : JinWishart.ComplexSample (m := m) (n := p)=>∑ i,JinWishart.positiveSpectrumLog (JinWishart.actualCorrelatedEigenvalue B M i z)
 Integrable (fun z=>(S z-(∫ w,S w ∂stdGaussian _))^2) (stdGaussian _) ∧
 (∫ z,(S z-(∫ w,S w ∂stdGaussian _))^2 ∂stdGaussian _) =
 (∫ z,(S z)^2 ∂stdGaussian _)-(∫ z,S z ∂stdGaussian _)^2
end
end SheafSingularLogSquare
open Lean Meta in
#eval show MetaM Unit from do
 for (target,expected) in [
 (`JinWishart.integrable_actualCorrelated_positive_log_sum_sq,`SheafSingularLogSquare.SumSquare),
 (`JinWishart.integrable_actualCorrelated_positive_log_sq,`SheafSingularLogSquare.ModeSquare),
 (`JinWishart.actualCorrelated_positive_log_sum_centered_second_moment,`SheafSingularLogSquare.Centered)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels target)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels expected)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF target type differs: {target}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
