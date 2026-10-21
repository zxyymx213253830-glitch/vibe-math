import JinWishartFormalization.ActualComplexPolynomialLog
import Lean
open Matrix MeasureTheory ProbabilityTheory
namespace SheafProperActual
noncomputable section
def PlanarNeg : Prop := ∀ {ι : Type} [Fintype ι] (P : MvPolynomial ι ℂ),
 Integrable (fun x => max 0 (-Real.log ‖MvPolynomial.eval x P‖))
  (Measure.pi (fun _ : ι => stdGaussian ℂ))
def PlanarLog : Prop := ∀ {ι : Type} [Fintype ι] (P : MvPolynomial ι ℂ),
 Integrable (fun x => Real.log ‖MvPolynomial.eval x P‖)
  (Measure.pi (fun _ : ι => stdGaussian ℂ))
def ProperLaw : Prop := ∀ (ι : Type) [Fintype ι],
 JinWishart.standardComplexPiLaw ι =
  (Measure.pi (fun _ : ι => stdGaussian ℂ)).map (fun z i => (Real.sqrt 2)⁻¹ • z i)
def ProperNeg : Prop := ∀ {ι : Type} [Fintype ι] (P : MvPolynomial ι ℂ),
 Integrable (fun x => max 0 (-Real.log ‖MvPolynomial.eval x P‖)) (JinWishart.standardComplexPiLaw ι)
def ProperLog : Prop := ∀ {ι : Type} [Fintype ι] (P : MvPolynomial ι ℂ),
 Integrable (fun x => Real.log ‖MvPolynomial.eval x P‖) (JinWishart.standardComplexPiLaw ι)
def ActualNeg : Prop := ∀ (m p : ℕ) (P : MvPolynomial (Fin m × Fin p) ℂ),
 Integrable (fun z => max 0 (-Real.log ‖MvPolynomial.eval (JinWishart.complexMatrixEntries z) P‖))
  (stdGaussian (JinWishart.ComplexSample (m := m) (n := p)))
def ActualLog : Prop := ∀ (m p : ℕ) (P : MvPolynomial (Fin m × Fin p) ℂ),
 Integrable (fun z => Real.log ‖MvPolynomial.eval (JinWishart.complexMatrixEntries z) P‖)
  (stdGaussian (JinWishart.ComplexSample (m := m) (n := p)))
def CompressedEval : Prop := ∀ {m p n q : ℕ}
 (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
 (L : Matrix (Fin q) (Fin m) ℂ) (H : Matrix (Fin n) (Fin q) ℂ)
 (z : JinWishart.ComplexSample (m := m) (n := p)),
 MvPolynomial.eval (JinWishart.complexMatrixEntries z) (JinWishart.entryAffineCompressedDet B M L H) =
  (L*(JinWishart.complexSampleMatrix z*B+M)*H).det
def CompressedNeg : Prop := ∀ {m p n q : ℕ}
 (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
 (L : Matrix (Fin q) (Fin m) ℂ) (H : Matrix (Fin n) (Fin q) ℂ),
 Integrable (fun z => max 0 (-Real.log ‖(L*(JinWishart.complexSampleMatrix z*B+M)*H).det‖))
  (stdGaussian (JinWishart.ComplexSample (m := m) (n := p)))
def CompressedLog : Prop := ∀ {m p n q : ℕ}
 (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
 (L : Matrix (Fin q) (Fin m) ℂ) (H : Matrix (Fin n) (Fin q) ℂ),
 Integrable (fun z => Real.log ‖(L*(JinWishart.complexSampleMatrix z*B+M)*H).det‖)
  (stdGaussian (JinWishart.ComplexSample (m := m) (n := p)))
end
end SheafProperActual
open Lean Meta in
#eval show MetaM Unit from do
 for (target,expected) in [
  (`JinWishart.stdGaussian_fintype_polynomial_negativeLog_integrable,`SheafProperActual.PlanarNeg),
  (`JinWishart.stdGaussian_fintype_polynomial_log_integrable,`SheafProperActual.PlanarLog),
  (`JinWishart.standardComplexPiLaw_eq_planarMap,`SheafProperActual.ProperLaw),
  (`JinWishart.properComplex_pi_polynomial_negativeLog_integrable,`SheafProperActual.ProperNeg),
  (`JinWishart.properComplex_pi_polynomial_log_integrable,`SheafProperActual.ProperLog),
  (`JinWishart.integrable_actualComplexMatrix_holomorphic_negativeLog,`SheafProperActual.ActualNeg),
  (`JinWishart.integrable_actualComplexMatrix_holomorphic_log,`SheafProperActual.ActualLog),
  (`JinWishart.entryAffineCompressedDet_eval,`SheafProperActual.CompressedEval),
  (`JinWishart.integrable_actualAffineCompressedDet_negativeLog,`SheafProperActual.CompressedNeg),
  (`JinWishart.integrable_actualAffineCompressedDet_log,`SheafProperActual.CompressedLog)] do
   let actualType ← inferType (← mkConstWithFreshMVarLevels target)
   let expectedType ← whnf (← mkConstWithFreshMVarLevels expected)
   unless ← isDefEq actualType expectedType do
    throwError "SHEAF target type differs: {target}"
 IO.println "SHEAF_TARGET_TYPES_EQ PASS"
