import JinWishartFormalization.CorrelatedGramTraceAlgebra

/-! Actual trace mean, two distinct second moments and centered variance of ZB+M.
Codex. Fixed arbitrary rectangular/singular B; no fullrank or density premise.
[需人工审查] Gaussian normalization, Fubini/real-integral transport and model.
-/
open Matrix MeasureTheory ProbabilityTheory
open scoped ComplexOrder
namespace JinWishart
noncomputable section

theorem eval_correlatedGram_trace {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (z : ComplexSample (m := m) (n := p)) :
    complexGaussianPolynomialEval (correlatedGramTracePolynomial B M) (complexMatrixEntries z) =
      (complexGram (complexSampleMatrix z*B+M)).trace := by
  classical
  let e := MvPolynomial.eval (Sum.elim (complexMatrixEntries z) (fun i => star (complexMatrixEntries z i)))
  change e (correlatedGramTracePolynomial B M) = _
  simp only [correlatedGramTracePolynomial,map_sum]
  change (∑ i, complexGaussianPolynomialEval (correlatedGramEntryPolynomial B M i i)
    (complexMatrixEntries z)) = _
  simp only [eval_correlatedGramEntryPolynomial,Matrix.trace,Matrix.diag]

theorem eval_correlatedGram_squaredTrace {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (z : ComplexSample (m := m) (n := p)) :
    complexGaussianPolynomialEval (correlatedGramSquaredTracePolynomial B M) (complexMatrixEntries z) =
      ((complexGram (complexSampleMatrix z*B+M))^2).trace := by
  classical
  let e := MvPolynomial.eval (Sum.elim (complexMatrixEntries z) (fun i => star (complexMatrixEntries z i)))
  change e (correlatedGramSquaredTracePolynomial B M) = _
  simp only [correlatedGramSquaredTracePolynomial,map_sum,map_mul]
  change (∑ i, ∑ j,
    complexGaussianPolynomialEval (correlatedGramEntryPolynomial B M i j) (complexMatrixEntries z)*
    complexGaussianPolynomialEval (correlatedGramEntryPolynomial B M j i) (complexMatrixEntries z)) = _
  simp only [eval_correlatedGramEntryPolynomial,pow_two,Matrix.trace,Matrix.diag,Matrix.mul_apply]

theorem eval_correlatedGram_trace_sq {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (z : ComplexSample (m := m) (n := p)) :
    complexGaussianPolynomialEval ((correlatedGramTracePolynomial B M)^2) (complexMatrixEntries z) =
      ((complexGram (complexSampleMatrix z*B+M)).trace)^2 := by
  let e := MvPolynomial.eval (Sum.elim (complexMatrixEntries z) (fun i => star (complexMatrixEntries z i)))
  change e ((correlatedGramTracePolynomial B M)^2) = _
  rw [map_pow]
  change (complexGaussianPolynomialEval (correlatedGramTracePolynomial B M) (complexMatrixEntries z))^2 = _
  rw [eval_correlatedGram_trace]

theorem integrable_actualCorrelatedGram_trace {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) :
    Integrable (fun z : ComplexSample (m := m) (n := p) =>
      (complexGram (complexSampleMatrix z*B+M)).trace.re) (stdGaussian _) := by
  have h := (integrable_actualComplexMatrix_polynomial m p (correlatedGramTracePolynomial B M)).re
  simpa only [RCLike.re_eq_complex_re,eval_correlatedGram_trace] using! h

theorem integral_actualCorrelatedGram_trace {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) :
    (∫ z : ComplexSample (m := m) (n := p),
      (complexGram (complexSampleMatrix z*B+M)).trace.re ∂stdGaussian _) =
      ((m : ℂ) • complexGram B+complexGram M).trace.re := by
  have hi := integrable_actualComplexMatrix_polynomial m p (correlatedGramTracePolynomial B M)
  have h := integral_actualComplexMatrix_polynomial m p (correlatedGramTracePolynomial B M)
  have hr : (∫ z : ComplexSample (m := m) (n := p),
      (complexGaussianPolynomialEval (correlatedGramTracePolynomial B M) (complexMatrixEntries z)).re ∂stdGaussian _) =
      (∫ z : ComplexSample (m := m) (n := p),
        complexGaussianPolynomialEval (correlatedGramTracePolynomial B M) (complexMatrixEntries z) ∂stdGaussian _).re := by
    simpa using! integral_re hi
  have he (z : ComplexSample (m := m) (n := p)) :
      (complexGaussianPolynomialEval (correlatedGramTracePolynomial B M) (complexMatrixEntries z)).re =
        (complexGram (complexSampleMatrix z*B+M)).trace.re :=
    congrArg Complex.re (eval_correlatedGram_trace B M z)
  simp_rw [he] at hr
  rw [hr,h,complexGaussianMoment_correlatedGram_trace]

theorem integrable_actualCorrelatedGram_squaredTrace {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) :
    Integrable (fun z : ComplexSample (m := m) (n := p) =>
      ((complexGram (complexSampleMatrix z*B+M))^2).trace.re) (stdGaussian _) := by
  have h := (integrable_actualComplexMatrix_polynomial m p (correlatedGramSquaredTracePolynomial B M)).re
  simpa only [RCLike.re_eq_complex_re,eval_correlatedGram_squaredTrace] using! h

theorem integral_actualCorrelatedGram_squaredTrace {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) :
    (∫ z : ComplexSample (m := m) (n := p),
      ((complexGram (complexSampleMatrix z*B+M))^2).trace.re ∂stdGaussian _) =
      (((m : ℂ) • complexGram B+complexGram M)^2).trace.re +
      (m : ℝ)*(complexGram B).trace.re^2+2*(complexGram B).trace.re*(complexGram M).trace.re := by
  have hi := integrable_actualComplexMatrix_polynomial m p (correlatedGramSquaredTracePolynomial B M)
  have h := integral_actualComplexMatrix_polynomial m p (correlatedGramSquaredTracePolynomial B M)
  have hr : (∫ z : ComplexSample (m := m) (n := p),
      (complexGaussianPolynomialEval (correlatedGramSquaredTracePolynomial B M) (complexMatrixEntries z)).re ∂stdGaussian _) =
      (∫ z : ComplexSample (m := m) (n := p),
        complexGaussianPolynomialEval (correlatedGramSquaredTracePolynomial B M) (complexMatrixEntries z) ∂stdGaussian _).re := by
    simpa using! integral_re hi
  have he (z : ComplexSample (m := m) (n := p)) :
      (complexGaussianPolynomialEval (correlatedGramSquaredTracePolynomial B M) (complexMatrixEntries z)).re =
        ((complexGram (complexSampleMatrix z*B+M))^2).trace.re :=
    congrArg Complex.re (eval_correlatedGram_squaredTrace B M z)
  simp_rw [he] at hr
  rw [hr,h,complexGaussianMoment_correlatedGram_squaredTrace]
  have hzS := (RCLike.nonneg_iff.mp (complexGram_posSemidef B).trace_nonneg).2
  have hzA := (RCLike.nonneg_iff.mp (complexGram_posSemidef M).trace_nonneg).2
  change (complexGram B).trace.im = 0 at hzS
  change (complexGram M).trace.im = 0 at hzA
  norm_num [Complex.add_re,Complex.mul_re,pow_two,hzS,hzA]

theorem correlatedGram_trace_sq_eval_re {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (z : ComplexSample (m := m) (n := p)) :
    (complexGaussianPolynomialEval ((correlatedGramTracePolynomial B M)^2) (complexMatrixEntries z)).re =
      ((complexGram (complexSampleMatrix z*B+M)).trace.re)^2 := by
  rw [eval_correlatedGram_trace_sq]
  have hz := (RCLike.nonneg_iff.mp (complexGram_posSemidef (complexSampleMatrix z*B+M)).trace_nonneg).2
  change (complexGram (complexSampleMatrix z*B+M)).trace.im = 0 at hz
  simp [pow_two,Complex.mul_re,hz]

theorem integrable_actualCorrelatedGram_trace_sq {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) :
    Integrable (fun z : ComplexSample (m := m) (n := p) =>
      ((complexGram (complexSampleMatrix z*B+M)).trace.re)^2) (stdGaussian _) := by
  have h := (integrable_actualComplexMatrix_polynomial m p ((correlatedGramTracePolynomial B M)^2)).re
  simpa only [RCLike.re_eq_complex_re,correlatedGram_trace_sq_eval_re] using! h

theorem integral_actualCorrelatedGram_trace_sq {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) :
    (∫ z : ComplexSample (m := m) (n := p),
      ((complexGram (complexSampleMatrix z*B+M)).trace.re)^2 ∂stdGaussian _) =
      (((m : ℂ) • complexGram B+complexGram M).trace.re)^2 +
      (m : ℝ)*((complexGram B)^2).trace.re+2*(complexGram B*complexGram M).trace.re := by
  have hi := integrable_actualComplexMatrix_polynomial m p ((correlatedGramTracePolynomial B M)^2)
  have h := integral_actualComplexMatrix_polynomial m p ((correlatedGramTracePolynomial B M)^2)
  have hr : (∫ z : ComplexSample (m := m) (n := p),
      (complexGaussianPolynomialEval ((correlatedGramTracePolynomial B M)^2) (complexMatrixEntries z)).re ∂stdGaussian _) =
      (∫ z : ComplexSample (m := m) (n := p),
        complexGaussianPolynomialEval ((correlatedGramTracePolynomial B M)^2) (complexMatrixEntries z) ∂stdGaussian _).re := by
    simpa using! integral_re hi
  simp_rw [correlatedGram_trace_sq_eval_re] at hr
  rw [hr,h,complexGaussianMoment_correlatedGram_trace_sq]
  have hzS := (RCLike.nonneg_iff.mp (complexGram_posSemidef B).trace_nonneg).2
  have hzA := (RCLike.nonneg_iff.mp (complexGram_posSemidef M).trace_nonneg).2
  change (complexGram B).trace.im = 0 at hzS
  change (complexGram M).trace.im = 0 at hzA
  have hzK : ((m : ℂ) • complexGram B+complexGram M).trace.im = 0 := by
    simp [Matrix.trace_add,Matrix.trace_smul,smul_eq_mul,Complex.add_im,Complex.mul_im,hzS,hzA]
  norm_num [Complex.add_re,Complex.mul_re,pow_two,hzK,hzS,hzA]

theorem integral_actualCorrelatedGram_trace_centered_sq {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) :
    (∫ z : ComplexSample (m := m) (n := p),
      ((complexGram (complexSampleMatrix z*B+M)).trace.re-
        ((m : ℂ) • complexGram B+complexGram M).trace.re)^2 ∂stdGaussian _) =
      (m : ℝ)*((complexGram B)^2).trace.re+2*(complexGram B*complexGram M).trace.re := by
  let T := ((m : ℂ) • complexGram B+complexGram M).trace.re
  have hi := integrable_actualCorrelatedGram_trace B M
  have hi2 := integrable_actualCorrelatedGram_trace_sq B M
  have he (z : ComplexSample (m := m) (n := p)) :
      ((complexGram (complexSampleMatrix z*B+M)).trace.re-T)^2 =
        ((complexGram (complexSampleMatrix z*B+M)).trace.re)^2-
          (2*T)*(complexGram (complexSampleMatrix z*B+M)).trace.re+T^2 := by ring
  change (∫ z, ((complexGram (complexSampleMatrix z*B+M)).trace.re-T)^2 ∂stdGaussian _) = _
  simp_rw [he]
  have ha := integral_add (hi2.sub (hi.const_mul (2*T))) (integrable_const (T^2))
  have hb := integral_sub hi2 (hi.const_mul (2*T))
  simp only [Pi.sub_apply,Pi.add_apply] at ha hb
  rw [ha,hb,integral_const_mul,integral_const,integral_actualCorrelatedGram_trace_sq,
    integral_actualCorrelatedGram_trace]
  simp only [measureReal_def,measure_univ,ENNReal.toReal_one,one_smul]
  dsimp only [T]
  ring

end
end JinWishart
#print axioms JinWishart.eval_correlatedGram_trace
#print axioms JinWishart.eval_correlatedGram_squaredTrace
#print axioms JinWishart.eval_correlatedGram_trace_sq
#print axioms JinWishart.integrable_actualCorrelatedGram_trace
#print axioms JinWishart.integral_actualCorrelatedGram_trace
#print axioms JinWishart.integrable_actualCorrelatedGram_squaredTrace
#print axioms JinWishart.integral_actualCorrelatedGram_squaredTrace
#print axioms JinWishart.correlatedGram_trace_sq_eval_re
#print axioms JinWishart.integrable_actualCorrelatedGram_trace_sq
#print axioms JinWishart.integral_actualCorrelatedGram_trace_sq
#print axioms JinWishart.integral_actualCorrelatedGram_trace_centered_sq
