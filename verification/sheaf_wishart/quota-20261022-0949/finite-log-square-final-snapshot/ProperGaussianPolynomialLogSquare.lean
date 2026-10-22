import JinWishartFormalization.FiniteGaussianPolynomialLogSquare
import JinWishartFormalization.ProperComplexGaussianPolynomialLog

/-! Log-square under arbitrary finite independent properCN1 coordinates.
Both real coordinates scale by1/sqrt2. Codex.
[需人工审查] Index/product transport and physical variance. -/
open MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

theorem stdGaussian_fintype_polynomial_log_sq_integrable
    {ι : Type*} [Fintype ι] (P : MvPolynomial ι ℂ) :
    Integrable (fun x=>(Real.log ‖MvPolynomial.eval x P‖)^2)
      (Measure.pi (fun _ : ι=>stdGaussian ℂ)) := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let E := MeasurableEquiv.piCongrLeft (fun _ : Fin (Fintype.card ι)=>ℂ) e
  have hp : MeasurePreserving E (Measure.pi (fun _ : ι=>stdGaussian ℂ))
      (Measure.pi (fun _ : Fin (Fintype.card ι)=>stdGaussian ℂ)) :=
    measurePreserving_piCongrLeft (fun _ : Fin (Fintype.card ι)=>stdGaussian ℂ) e
  have hi := stdGaussian_pi_mvPolynomial_log_sq_integrable (Fintype.card ι) (MvPolynomial.rename e P)
  have hb := hp.integrable_comp_of_integrable hi
  simpa [Function.comp_def,MvPolynomial.eval_rename,E,MeasurableEquiv.coe_piCongrLeft] using hb

theorem properComplex_pi_polynomial_log_sq_integrable
    {ι : Type*} [Fintype ι] (P : MvPolynomial ι ℂ) :
    Integrable (fun x=>(Real.log ‖MvPolynomial.eval x P‖)^2) (standardComplexPiLaw ι) := by
  let s : ℝ := (Real.sqrt 2)⁻¹
  let Q : MvPolynomial ι ℂ := MvPolynomial.eval₂ MvPolynomial.C
    (fun i=>MvPolynomial.C (s : ℂ)*MvPolynomial.X i) P
  have hC (x : ι→ℂ) : (MvPolynomial.eval x).comp (MvPolynomial.C : ℂ→+*MvPolynomial ι ℂ)=RingHom.id ℂ := by
    ext c
    simp
  have heval (x : ι→ℂ) : MvPolynomial.eval x Q=MvPolynomial.eval (fun i=>s • x i) P := by
    simp [Q,MvPolynomial.eval_eval₂,hC,Complex.real_smul]
  have hscale : Continuous (fun z : ι→ℂ=>fun i=>s • z i) := by fun_prop
  rw [standardComplexPiLaw_eq_planarMap]
  apply (integrable_map_measure ((MvPolynomial.continuous_eval P).norm.measurable.log.pow_const 2).aestronglyMeasurable
    hscale.measurable.aemeasurable).mpr
  change Integrable (fun x : ι→ℂ=>(Real.log ‖MvPolynomial.eval (fun i=>s • x i) P‖)^2) _
  simpa only [heval] using stdGaussian_fintype_polynomial_log_sq_integrable Q

end
end JinWishart
#print axioms JinWishart.stdGaussian_fintype_polynomial_log_sq_integrable
#print axioms JinWishart.properComplex_pi_polynomial_log_sq_integrable
