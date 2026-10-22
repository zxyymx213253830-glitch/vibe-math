import JinWishartFormalization.ComplexGaussianPolynomialLogSquare
import Lean
open MeasureTheory ProbabilityTheory Set Finset
namespace SheafLogMoment
noncomputable section
def Gamma : Prop := ∀ q : ℕ,IntegrableOn (fun t : ℝ=>t^q*Real.exp (-t)) (Ioi 0) ∧
 (∫ t : ℝ in Ioi 0,t^q*Real.exp (-t))=(q.factorial : ℝ)
def SmallballMoments : Prop := ∀ {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
 (f : α→ℝ),Measurable f → ∀ C : ℝ,0≤C →
 (∀ x : ℝ,0<x → μ.real {a | f a≤x}≤C*x) → ∀ q : ℕ,
 Integrable (fun a=>(max 0 (-Real.log (f a)))^(q+1)) μ ∧
 (∫ a,(max 0 (-Real.log (f a)))^(q+1) ∂μ)≤C*((q+1).factorial : ℝ)
def Disk : Prop := ∀ a : ℂ,∀ x : ℝ,0<x → (stdGaussian ℂ).real {z : ℂ | ‖z-a‖^2≤x}≤(1/2)*x
def RootMoments : Prop := ∀ a : ℂ,∀ q : ℕ,
 Integrable (fun z : ℂ=>(JinWishart.complexNegativeLog (z-a))^(q+1)) (stdGaussian ℂ) ∧
 (∫ z : ℂ,(JinWishart.complexNegativeLog (z-a))^(q+1) ∂stdGaussian ℂ)≤((q+1).factorial : ℝ)/(2*2^(q+1))
def RootSquare : Prop := ∀ a : ℂ,
 Integrable (fun z : ℂ=>(JinWishart.complexNegativeLog (z-a))^2) (stdGaussian ℂ) ∧
 (∫ z : ℂ,(JinWishart.complexNegativeLog (z-a))^2 ∂stdGaussian ℂ)≤1/4
def Product : Prop := ∀ {ι : Type*} (s : Finset ι) (f : ι→ℂ),
 JinWishart.complexNegativeLog (∏ i∈s,f i)≤∑ i∈s,JinWishart.complexNegativeLog (f i)
def Roots : Prop := ∀ {ι : Type*} [Fintype ι] (roots : ι→ℂ),
 Integrable (fun z : ℂ=>(JinWishart.complexNegativeLog (∏ i,(z-roots i)))^2) (stdGaussian ℂ) ∧
 (∫ z : ℂ,(JinWishart.complexNegativeLog (∏ i,(z-roots i)))^2 ∂stdGaussian ℂ)≤(Fintype.card ι : ℝ)^2/4
def Polynomial : Prop := ∀ P : Polynomial ℂ,
 Integrable (fun z : ℂ=>(JinWishart.complexNegativeLog (P.eval z))^2) (stdGaussian ℂ) ∧
 (∫ z : ℂ,(JinWishart.complexNegativeLog (P.eval z))^2 ∂stdGaussian ℂ)≤
 2*(JinWishart.complexNegativeLog P.leadingCoeff)^2+(P.natDegree : ℝ)^2/2
end
end SheafLogMoment
open Lean Meta in
#eval show MetaM Unit from do
 for (target,expected) in [
 (`JinWishart.integral_natPower_exp_neg_Ioi,`SheafLogMoment.Gamma),
 (`JinWishart.negativeLog_natPower_integrable_integral_le_of_smallball,`SheafLogMoment.SmallballMoments),
 (`JinWishart.stdGaussian_complex_squared_distance_smallball,`SheafLogMoment.Disk),
 (`JinWishart.stdGaussian_complex_negativeLog_natPower_uniform_root,`SheafLogMoment.RootMoments),
 (`JinWishart.stdGaussian_complex_negativeLog_sq_uniform_root,`SheafLogMoment.RootSquare),
 (`JinWishart.complexNegativeLog_finset_prod_le_sum,`SheafLogMoment.Product),
 (`JinWishart.stdGaussian_complex_finite_rootProduct_negativeLog_sq,`SheafLogMoment.Roots),
 (`JinWishart.stdGaussian_complex_polynomial_negativeLog_sq,`SheafLogMoment.Polynomial)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels target)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels expected)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF target type differs: {target}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
