import JinWishartFormalization.GaussianPolynomialSectionLogSquare
import JinWishartFormalization.FiniteComplexGaussianPolynomialLog

/-! Finite-dimensional holomorphic Gaussian polynomial log-square integrability.
Planar stdGaussian(C) secondmoment2. Real.log0=0; includes zero polynomial.
Codex. [需人工审查] Product splitting, AE leading coefficient and Fubini. -/
open MeasureTheory ProbabilityTheory Filter
namespace JinWishart
noncomputable section

theorem stdGaussian_pi_mvPolynomial_negativeLog_sq_integrable :
    ∀ n (P : MvPolynomial (Fin n) ℂ),
      Integrable (fun x=>(complexNegativeLog (MvPolynomial.eval x P))^2)
        (Measure.pi (fun _ : Fin n=>stdGaussian ℂ)) := by
  intro n
  induction n with
  | zero =>
    intro P
    have hc : P=MvPolynomial.C (P.coeff 0) := MvPolynomial.eq_C_of_isEmpty P
    rw [hc]
    simp only [MvPolynomial.eval_C]
    exact integrable_const _
  | succ n ih =>
    intro P
    classical
    by_cases hP : P=0
    · subst P
      simp [complexNegativeLog]
    let q := MvPolynomial.finSuccEquiv ℂ n P
    have hq : q≠0 := fun h=>hP ((MvPolynomial.finSuccEquiv ℂ n).injective h)
    have hae := stdGaussian_pi_mvPolynomial_ne_zero_ae n q.leadingCoeff
      (Polynomial.leadingCoeff_ne_zero.mpr hq)
    have heq : (fun y=>(complexNegativeLog (Polynomial.map (MvPolynomial.eval y) q).leadingCoeff)^2)
        =ᵐ[Measure.pi (fun _ : Fin n=>stdGaussian ℂ)]
        (fun y=>(complexNegativeLog (MvPolynomial.eval y q.leadingCoeff))^2) := by
      filter_upwards [hae] with y hy
      rw [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hy]
    have hcoeff := (ih q.leadingCoeff).congr heq.symm
    have hcont : Continuous (fun w : (Fin n → ℂ) × ℂ => MvPolynomial.eval (Fin.cons w.2 w.1) P) := by
      apply (MvPolynomial.continuous_eval P).comp
      apply continuous_pi
      intro i
      refine Fin.cases continuous_snd ?_ i
      intro j
      exact (continuous_apply j).comp continuous_fst
    have heval (w : (Fin n → ℂ) × ℂ) : (Polynomial.map (MvPolynomial.eval w.1) q).eval w.2=
        MvPolynomial.eval (Fin.cons w.2 w.1) P := (MvPolynomial.eval_eq_eval_mv_eval' w.1 w.2 P).symm
    have hm : Measurable (fun w : (Fin n → ℂ) × ℂ => (Polynomial.map (MvPolynomial.eval w.1) q).eval w.2) := by
      simpa only [heval] using hcont.measurable
    have hs := (integrable_polynomial_section_negativeLog_sq
      (Measure.pi (fun _ : Fin n=>stdGaussian ℂ)) (fun y=>Polynomial.map (MvPolynomial.eval y) q)
      hm hcoeff q.natDegree (ae_of_all _ (fun _=>Polynomial.natDegree_map_le))).1
    have hb := (planarGaussianSplit_measurePreserving n).integrable_comp_of_integrable hs
    simpa only [Function.comp_def,heval,planarGaussianSplit_cons] using hb

theorem integrable_stdGaussian_pi_mvPolynomial_norm_sq (n : ℕ) (P : MvPolynomial (Fin n) ℂ) :
    Integrable (fun x=>‖MvPolynomial.eval x P‖^2) (Measure.pi (fun _ : Fin n=>stdGaussian ℂ)) := by
  apply (integrable_stdGaussian_pi_mvPolynomial_eval n (P^2)).norm.congr
  exact ae_of_all _ (fun x=>by dsimp only; rw [MvPolynomial.eval_pow,norm_pow])

theorem real_log_sq_le_nonnegative_square (u : ℝ) (hu : 0≤u) :
    (Real.log u)^2≤2*u^2+2*(max 0 (-Real.log u))^2 := by
  by_cases hz : u=0
  · simp [hz]
  have hp : 0<u := lt_of_le_of_ne hu (Ne.symm hz)
  have hlog := Real.log_le_sub_one_of_pos hp
  have h1 := le_max_left (0:ℝ) (-Real.log u)
  have h2 := le_max_right (0:ℝ) (-Real.log u)
  have habs : |Real.log u|≤u+max 0 (-Real.log u) := abs_le.mpr ⟨by linarith,by linarith⟩
  have hs := pow_le_pow_left₀ (abs_nonneg _) habs 2
  rw [sq_abs] at hs
  nlinarith [sq_nonneg (u-max 0 (-Real.log u))]

theorem stdGaussian_pi_mvPolynomial_log_sq_integrable (n : ℕ) (P : MvPolynomial (Fin n) ℂ) :
    Integrable (fun x=>(Real.log ‖MvPolynomial.eval x P‖)^2)
      (Measure.pi (fun _ : Fin n=>stdGaussian ℂ)) := by
  have hnorm := integrable_stdGaussian_pi_mvPolynomial_norm_sq n P
  have hneg := stdGaussian_pi_mvPolynomial_negativeLog_sq_integrable n P
  apply ((hnorm.const_mul 2).add (hneg.const_mul 2)).mono'
    ((MvPolynomial.continuous_eval P).norm.measurable.log.pow_const 2).aestronglyMeasurable
  exact ae_of_all _ (fun x=>by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact real_log_sq_le_nonnegative_square _ (norm_nonneg _))

end
end JinWishart
#print axioms JinWishart.stdGaussian_pi_mvPolynomial_negativeLog_sq_integrable
#print axioms JinWishart.integrable_stdGaussian_pi_mvPolynomial_norm_sq
#print axioms JinWishart.real_log_sq_le_nonnegative_square
#print axioms JinWishart.stdGaussian_pi_mvPolynomial_log_sq_integrable
