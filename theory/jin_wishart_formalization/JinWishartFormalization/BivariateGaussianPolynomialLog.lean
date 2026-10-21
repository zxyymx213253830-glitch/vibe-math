import JinWishartFormalization.GaussianPolynomialSectionLog

/-! Two independent planar Gaussians, each with two variance-one real coordinates.
The polynomial is nested Polynomial(Polynomial C). Real.log0=0 throughout.
Leading coefficients may vanish on fibers; only an AE identification is used.
Codex. [需人工审查] Gaussian null sets, product measure, Fubini and model interpretation.
-/
open MeasureTheory ProbabilityTheory Filter
namespace JinWishart
noncomputable section

def complexBivariateEval (P : Polynomial (Polynomial ℂ)) (w : ℂ × ℂ) : ℂ :=
  (P.map (Polynomial.evalRingHom w.1)).eval w.2

theorem stdGaussian_complex_polynomial_eval_ne_zero_ae (P : Polynomial ℂ) (hP : P≠0) :
    ∀ᵐ z ∂stdGaussian ℂ, P.eval z ≠ 0 := by
  haveI : NullSingletonClass (stdGaussian ℂ) := by
    rw [stdGaussian_complex_eq_radialDensity]
    infer_instance
  have hfin : Set.Finite {z : ℂ | P.eval z=0} :=
    Polynomial.finite_setOfPred_isRoot hP
  simpa only [ae_iff,not_not] using hfin.measure_zero (stdGaussian ℂ)

theorem complexBivariateEval_eq_sum (P : Polynomial (Polynomial ℂ)) (w : ℂ × ℂ) :
    complexBivariateEval P w = ∑ k ∈ P.support, (P.coeff k).eval w.1 * w.2^k := by
  simp [complexBivariateEval,Polynomial.eval_map,Polynomial.eval₂_eq_sum,Polynomial.sum_def]

theorem continuous_complexBivariateEval (P : Polynomial (Polynomial ℂ)) :
    Continuous (complexBivariateEval P) := by
  change Continuous (fun w : ℂ × ℂ => complexBivariateEval P w)
  simp_rw [complexBivariateEval_eq_sum]
  apply continuous_finsetSum
  intro k _
  fun_prop

theorem stdGaussian_bivariate_polynomial_negativeLog (P : Polynomial (Polynomial ℂ)) :
    Integrable (fun w : ℂ × ℂ => complexNegativeLog (complexBivariateEval P w))
      ((stdGaussian ℂ).prod (stdGaussian ℂ)) ∧
    (∫ w : ℂ × ℂ, complexNegativeLog (complexBivariateEval P w)
      ∂(stdGaussian ℂ).prod (stdGaussian ℂ)) ≤
      complexNegativeLog P.leadingCoeff.leadingCoeff+
        (P.leadingCoeff.natDegree : ℝ)/4+(P.natDegree : ℝ)/4 := by
  classical
  by_cases hP : P=0
  · subst P
    simp [complexBivariateEval,complexNegativeLog]
  have hlead : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  have hae := stdGaussian_complex_polynomial_eval_ne_zero_ae P.leadingCoeff hlead
  have heq : (fun a : ℂ => complexNegativeLog (P.map (Polynomial.evalRingHom a)).leadingCoeff)
      =ᵐ[stdGaussian ℂ] (fun a => complexNegativeLog (P.leadingCoeff.eval a)) := by
    filter_upwards [hae] with a ha
    rw [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ ha]
    rfl
  have hcoeff := ((stdGaussian_complex_polynomial_negativeLog P.leadingCoeff).1).congr heq.symm
  have hs := integrable_polynomial_section_negativeLog (stdGaussian ℂ)
    (fun a => P.map (Polynomial.evalRingHom a)) (continuous_complexBivariateEval P).measurable
    hcoeff P.natDegree (ae_of_all _ (fun _a => Polynomial.natDegree_map_le))
  refine ⟨hs.1, ?_⟩
  have heqi := integral_congr_ae heq
  calc
    _ ≤ (∫ a : ℂ, complexNegativeLog (P.leadingCoeff.eval a) ∂stdGaussian ℂ)+
        (P.natDegree : ℝ)/4 := by simpa only [heqi,complexBivariateEval] using hs.2
    _ ≤ (complexNegativeLog P.leadingCoeff.leadingCoeff+(P.leadingCoeff.natDegree : ℝ)/4)+
        (P.natDegree : ℝ)/4 :=
      add_le_add (stdGaussian_complex_polynomial_negativeLog P.leadingCoeff).2 le_rfl
    _ = _ := by ring

theorem integrable_stdGaussian_bivariate_polynomial_eval (P : Polynomial (Polynomial ℂ)) :
    Integrable (complexBivariateEval P) ((stdGaussian ℂ).prod (stdGaussian ℂ)) := by
  classical
  change Integrable (fun w : ℂ × ℂ => complexBivariateEval P w) _
  simp_rw [complexBivariateEval_eq_sum]
  apply integrable_finsetSum
  intro k _
  have hk : Integrable (fun z : ℂ => z^k) (stdGaussian ℂ) := by
    simpa using integrable_stdGaussian_complex_polynomial_eval ((Polynomial.X : Polynomial ℂ)^k)
  exact (integrable_stdGaussian_complex_polynomial_eval (P.coeff k)).mul_prod hk

theorem stdGaussian_bivariate_polynomial_log_integrable (P : Polynomial (Polynomial ℂ)) :
    Integrable (fun w : ℂ × ℂ => Real.log ‖complexBivariateEval P w‖)
      ((stdGaussian ℂ).prod (stdGaussian ℂ)) := by
  have hf := (integrable_stdGaussian_bivariate_polynomial_eval P).norm
  have hn := (stdGaussian_bivariate_polynomial_negativeLog P).1
  apply (hf.add hn).mono'
    (continuous_complexBivariateEval P).norm.measurable.log.aestronglyMeasurable
  filter_upwards [] with w
  rw [Real.norm_eq_abs]
  change |Real.log ‖complexBivariateEval P w‖| ≤
    ‖complexBivariateEval P w‖+max 0 (-Real.log ‖complexBivariateEval P w‖)
  by_cases hz : complexBivariateEval P w=0
  · simp [hz]
  have hu := Real.log_le_sub_one_of_pos (norm_pos_iff.mpr hz)
  have h1 := le_max_left (0 : ℝ) (-Real.log ‖complexBivariateEval P w‖)
  have h2 := le_max_right (0 : ℝ) (-Real.log ‖complexBivariateEval P w‖)
  have hnorm := norm_nonneg (complexBivariateEval P w)
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end
end JinWishart
#print axioms JinWishart.stdGaussian_complex_polynomial_eval_ne_zero_ae
#print axioms JinWishart.complexBivariateEval_eq_sum
#print axioms JinWishart.continuous_complexBivariateEval
#print axioms JinWishart.stdGaussian_bivariate_polynomial_negativeLog
#print axioms JinWishart.integrable_stdGaussian_bivariate_polynomial_eval
#print axioms JinWishart.stdGaussian_bivariate_polynomial_log_integrable
