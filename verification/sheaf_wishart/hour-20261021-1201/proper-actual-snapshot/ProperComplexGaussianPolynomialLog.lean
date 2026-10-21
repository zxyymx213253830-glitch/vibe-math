import JinWishartFormalization.FiniteComplexGaussianPolynomialLog
import JinWishartFormalization.GaussianMatrixPolynomialLaw
import Mathlib.Algebra.MvPolynomial.Rename

/-! Polynomial logarithms for the actual proper CN(0,1) product measure.
The factor (sqrt2)^-1 acts on BOTH real coordinates. All polynomials are fixed
and holomorphic. Real.log0=0 is totalized, including the identically zero case.
Codex. [需人工审查] Product/index transport, measurability and physical variance.
-/
open MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

theorem stdGaussian_fintype_polynomial_negativeLog_integrable
    {ι : Type*} [Fintype ι] (P : MvPolynomial ι ℂ) :
    Integrable (fun x => complexNegativeLog (MvPolynomial.eval x P))
      (Measure.pi (fun _ : ι => stdGaussian ℂ)) := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let E := MeasurableEquiv.piCongrLeft (fun _ : Fin (Fintype.card ι) => ℂ) e
  have hp : MeasurePreserving E (Measure.pi (fun _ : ι => stdGaussian ℂ))
      (Measure.pi (fun _ : Fin (Fintype.card ι) => stdGaussian ℂ)) :=
    measurePreserving_piCongrLeft (fun _ : Fin (Fintype.card ι) => stdGaussian ℂ) e
  have hi := stdGaussian_pi_mvPolynomial_negativeLog_integrable
    (Fintype.card ι) (MvPolynomial.rename e P)
  have hb := hp.integrable_comp_of_integrable hi
  simpa [Function.comp_def,MvPolynomial.eval_rename,E,MeasurableEquiv.coe_piCongrLeft] using hb

theorem stdGaussian_fintype_polynomial_log_integrable
    {ι : Type*} [Fintype ι] (P : MvPolynomial ι ℂ) :
    Integrable (fun x => Real.log ‖MvPolynomial.eval x P‖)
      (Measure.pi (fun _ : ι => stdGaussian ℂ)) := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let E := MeasurableEquiv.piCongrLeft (fun _ : Fin (Fintype.card ι) => ℂ) e
  have hp : MeasurePreserving E (Measure.pi (fun _ : ι => stdGaussian ℂ))
      (Measure.pi (fun _ : Fin (Fintype.card ι) => stdGaussian ℂ)) :=
    measurePreserving_piCongrLeft (fun _ : Fin (Fintype.card ι) => stdGaussian ℂ) e
  have hi := stdGaussian_pi_mvPolynomial_log_integrable
    (Fintype.card ι) (MvPolynomial.rename e P)
  have hb := hp.integrable_comp_of_integrable hi
  simpa [Function.comp_def,MvPolynomial.eval_rename,E,MeasurableEquiv.coe_piCongrLeft] using hb

theorem standardComplexPiLaw_eq_planarMap (ι : Type*) [Fintype ι] :
    standardComplexPiLaw ι =
      (Measure.pi (fun _ : ι => stdGaussian ℂ)).map
        (fun z i => (Real.sqrt 2)⁻¹ • z i) := by
  unfold standardComplexPiLaw standardComplexScalarLaw
  exact (Measure.pi_map_pi (fun _ => (by fun_prop))).symm

theorem properComplex_pi_polynomial_negativeLog_integrable
    {ι : Type*} [Fintype ι] (P : MvPolynomial ι ℂ) :
    Integrable (fun x => complexNegativeLog (MvPolynomial.eval x P))
      (standardComplexPiLaw ι) := by
  let s : ℝ := (Real.sqrt 2)⁻¹
  let Q : MvPolynomial ι ℂ := MvPolynomial.eval₂ MvPolynomial.C
    (fun i => MvPolynomial.C (s : ℂ) * MvPolynomial.X i) P
  have hC (x : ι → ℂ) :
      (MvPolynomial.eval x).comp (MvPolynomial.C : ℂ →+* MvPolynomial ι ℂ) = RingHom.id ℂ := by
    ext c
    simp
  have heval (x : ι → ℂ) :
      MvPolynomial.eval x Q = MvPolynomial.eval (fun i => s • x i) P := by
    simp [Q,MvPolynomial.eval_eval₂,hC,Complex.real_smul]
  have hscale : Continuous (fun z : ι → ℂ => fun i => s • z i) := by fun_prop
  rw [standardComplexPiLaw_eq_planarMap]
  apply (integrable_map_measure
    (measurable_const.max (MvPolynomial.continuous_eval P).norm.measurable.log.neg).aestronglyMeasurable
    hscale.measurable.aemeasurable).mpr
  change Integrable (fun x : ι → ℂ => complexNegativeLog (MvPolynomial.eval (fun i => s • x i) P)) _
  simpa only [heval] using stdGaussian_fintype_polynomial_negativeLog_integrable Q

theorem properComplex_pi_polynomial_log_integrable
    {ι : Type*} [Fintype ι] (P : MvPolynomial ι ℂ) :
    Integrable (fun x => Real.log ‖MvPolynomial.eval x P‖)
      (standardComplexPiLaw ι) := by
  let s : ℝ := (Real.sqrt 2)⁻¹
  let Q : MvPolynomial ι ℂ := MvPolynomial.eval₂ MvPolynomial.C
    (fun i => MvPolynomial.C (s : ℂ) * MvPolynomial.X i) P
  have hC (x : ι → ℂ) :
      (MvPolynomial.eval x).comp (MvPolynomial.C : ℂ →+* MvPolynomial ι ℂ) = RingHom.id ℂ := by
    ext c
    simp
  have heval (x : ι → ℂ) :
      MvPolynomial.eval x Q = MvPolynomial.eval (fun i => s • x i) P := by
    simp [Q,MvPolynomial.eval_eval₂,hC,Complex.real_smul]
  have hscale : Continuous (fun z : ι → ℂ => fun i => s • z i) := by fun_prop
  rw [standardComplexPiLaw_eq_planarMap]
  apply (integrable_map_measure (MvPolynomial.continuous_eval P).norm.measurable.log.aestronglyMeasurable
    hscale.measurable.aemeasurable).mpr
  change Integrable (fun x : ι → ℂ => Real.log ‖MvPolynomial.eval (fun i => s • x i) P‖) _
  simpa only [heval] using stdGaussian_fintype_polynomial_log_integrable Q

end
end JinWishart
#print axioms JinWishart.stdGaussian_fintype_polynomial_negativeLog_integrable
#print axioms JinWishart.stdGaussian_fintype_polynomial_log_integrable
#print axioms JinWishart.standardComplexPiLaw_eq_planarMap
#print axioms JinWishart.properComplex_pi_polynomial_negativeLog_integrable
#print axioms JinWishart.properComplex_pi_polynomial_log_integrable
