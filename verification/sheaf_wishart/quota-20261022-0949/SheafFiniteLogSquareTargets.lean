import JinWishartFormalization.ActualComplexPolynomialLogSquare
import Lean
open Matrix MeasureTheory ProbabilityTheory Filter
namespace SheafFiniteLogSquare
noncomputable section
def Section : Prop := ∀ {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
 (P : α → Polynomial ℂ),Measurable (fun w : α × ℂ => (P w.1).eval w.2) →
 Integrable (fun a=>(JinWishart.complexNegativeLog (P a).leadingCoeff)^2) μ →
 ∀ D : ℕ,(∀ᵐ a ∂μ,(P a).natDegree≤D) →
 Integrable (fun w : α × ℂ => (JinWishart.complexNegativeLog ((P w.1).eval w.2))^2) (μ.prod (stdGaussian ℂ)) ∧
 (∫ w : α × ℂ,(JinWishart.complexNegativeLog ((P w.1).eval w.2))^2 ∂μ.prod (stdGaussian ℂ))≤
 2*(∫ a,(JinWishart.complexNegativeLog (P a).leadingCoeff)^2 ∂μ)+(D : ℝ)^2/2
def FiniteNegative : Prop := ∀ n (P : MvPolynomial (Fin n) ℂ),
 Integrable (fun x=>(JinWishart.complexNegativeLog (MvPolynomial.eval x P))^2) (Measure.pi (fun _ : Fin n=>stdGaussian ℂ))
def FiniteNorm : Prop := ∀ n (P : MvPolynomial (Fin n) ℂ),
 Integrable (fun x=>‖MvPolynomial.eval x P‖^2) (Measure.pi (fun _ : Fin n=>stdGaussian ℂ))
def ScalarBound : Prop := ∀ u : ℝ,0≤u → (Real.log u)^2≤2*u^2+2*(max 0 (-Real.log u))^2
def FiniteLog : Prop := ∀ n (P : MvPolynomial (Fin n) ℂ),
 Integrable (fun x=>(Real.log ‖MvPolynomial.eval x P‖)^2) (Measure.pi (fun _ : Fin n=>stdGaussian ℂ))
def FintypeLog : Prop := ∀ {ι : Type*} [Fintype ι] (P : MvPolynomial ι ℂ),
 Integrable (fun x=>(Real.log ‖MvPolynomial.eval x P‖)^2) (Measure.pi (fun _ : ι=>stdGaussian ℂ))
def ProperLog : Prop := ∀ {ι : Type*} [Fintype ι] (P : MvPolynomial ι ℂ),
 Integrable (fun x=>(Real.log ‖MvPolynomial.eval x P‖)^2) (JinWishart.standardComplexPiLaw ι)
def Actual : Prop := ∀ m p : ℕ,∀ P : MvPolynomial (Fin m × Fin p) ℂ,
 Integrable (fun z=>(Real.log ‖MvPolynomial.eval (JinWishart.complexMatrixEntries z) P‖)^2)
 (stdGaussian (JinWishart.ComplexSample (m := m) (n := p)))
def Compressed : Prop := ∀ {m p n q : ℕ} (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
 (L : Matrix (Fin q) (Fin m) ℂ) (H : Matrix (Fin n) (Fin q) ℂ),
 Integrable (fun z=>(Real.log ‖(L*(JinWishart.complexSampleMatrix z*B+M)*H).det‖)^2)
 (stdGaussian (JinWishart.ComplexSample (m := m) (n := p)))
end
end SheafFiniteLogSquare
open Lean Meta in
#eval show MetaM Unit from do
 for (target,expected) in [
 (`JinWishart.integrable_polynomial_section_negativeLog_sq,`SheafFiniteLogSquare.Section),
 (`JinWishart.stdGaussian_pi_mvPolynomial_negativeLog_sq_integrable,`SheafFiniteLogSquare.FiniteNegative),
 (`JinWishart.integrable_stdGaussian_pi_mvPolynomial_norm_sq,`SheafFiniteLogSquare.FiniteNorm),
 (`JinWishart.real_log_sq_le_nonnegative_square,`SheafFiniteLogSquare.ScalarBound),
 (`JinWishart.stdGaussian_pi_mvPolynomial_log_sq_integrable,`SheafFiniteLogSquare.FiniteLog),
 (`JinWishart.stdGaussian_fintype_polynomial_log_sq_integrable,`SheafFiniteLogSquare.FintypeLog),
 (`JinWishart.properComplex_pi_polynomial_log_sq_integrable,`SheafFiniteLogSquare.ProperLog),
 (`JinWishart.integrable_actualComplexMatrix_holomorphic_log_sq,`SheafFiniteLogSquare.Actual),
 (`JinWishart.integrable_actualAffineCompressedDet_log_sq,`SheafFiniteLogSquare.Compressed)] do
  let actualType ← inferType (← mkConstWithFreshMVarLevels target)
  let expectedType ← whnf (← mkConstWithFreshMVarLevels expected)
  unless ← isDefEq actualType expectedType do
   throwError "SHEAF target type differs: {target}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
