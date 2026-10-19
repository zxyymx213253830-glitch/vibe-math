import JinWishartFormalization.ActualLogDetLowScaleCurvature
import JinWishartFormalization.NoncentralGramPolynomialMoments
import JinWishartFormalization.HermitianSquaredTrace

/-! An exact finite factorial-functional coefficient for actual logdet curvature.
Codex. Eliminates spectral probability integrals from the coefficient. This is
not yet its classical simplified shape/mean formula, nor a joint spectral law.
[需人工审查] Actual Gaussian polynomial transport, finite sums and model mapping.
-/
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace JinWishart
noncomputable section

def noncentralGramSquaredTracePolynomial {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) :
    ComplexMatrixPolynomial m n := ((noncentralGramEntryPolynomial M)^2).trace

theorem eval_noncentralGramSquaredTracePolynomial {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (z : ComplexSample (m := m) (n := n)) :
    complexGaussianPolynomialEval (noncentralGramSquaredTracePolynomial M) (complexMatrixEntries z) =
      ((complexGram (complexSampleMatrix z+M))^2).trace := by
  classical
  let e := MvPolynomial.eval (Sum.elim (complexMatrixEntries z) (fun i => star (complexMatrixEntries z i)))
  change e (((noncentralGramEntryPolynomial M)^2).trace) = _
  rw [AddMonoidHom.map_trace,Matrix.map_pow]
  have hm : (noncentralGramEntryPolynomial M).map e = complexGram (complexSampleMatrix z+M) := by
    ext i j
    exact eval_noncentralGramEntryPolynomial M z i j
  rw [hm]

theorem integral_actualNoncentralGram_squaredTrace {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) :
    (∫ z : ComplexSample (m := m) (n := n), ((complexGram (complexSampleMatrix z+M))^2).trace.re
      ∂stdGaussian _) = (complexGaussianPolynomialMoment (noncentralGramSquaredTracePolynomial M)).re := by
  have hi := integrable_actualComplexMatrix_polynomial m n (noncentralGramSquaredTracePolynomial M)
  have h := congrArg Complex.re
    (integral_actualComplexMatrix_polynomial m n (noncentralGramSquaredTracePolynomial M))
  have hr : (∫ z : ComplexSample (m := m) (n := n),
      (complexGaussianPolynomialEval (noncentralGramSquaredTracePolynomial M) (complexMatrixEntries z)).re
      ∂stdGaussian _) =
      (∫ z : ComplexSample (m := m) (n := n),
        complexGaussianPolynomialEval (noncentralGramSquaredTracePolynomial M) (complexMatrixEntries z)
        ∂stdGaussian _).re := by simpa using! integral_re hi
  rw [← hr] at h
  simp_rw [eval_noncentralGramSquaredTracePolynomial] at h
  exact h

theorem sum_integral_actualNoncentralEigenvalue_sq_eq_finite {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) :
    (∑ i, ∫ z, (complexNoncentralSampleEigenvalue M i z)^2 ∂stdGaussian _) =
      (complexGaussianPolynomialMoment (noncentralGramSquaredTracePolynomial M)).re := by
  rw [← integral_finsetSum _ (fun i _ => integrable_actualNoncentralEigenvalue_sq M i)]
  have he (z : ComplexSample (m := m) (n := n)) :
      (∑ i, (complexNoncentralSampleEigenvalue M i z)^2) =
        ((complexGram (complexSampleMatrix z+M))^2).trace.re :=
    (hermitian_trace_square_eq_orderedEigenvalues _ (complexGram_posSemidef _).1).symm
  simp_rw [he]
  exact integral_actualNoncentralGram_squaredTrace M

theorem actualNoncentralMatrixLogDet_low_scale_finite_curvature {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) :
    Tendsto (fun r : ℝ =>
      (r*((m*n : ℕ)+∑ i, ∑ j, ‖M i j‖^2)-
        (∫ z, actualNoncentralMatrixLogDet M r z ∂stdGaussian _))/r^2)
      (𝓝[>] 0)
      (𝓝 ((complexGaussianPolynomialMoment (noncentralGramSquaredTracePolynomial M)).re/2)) := by
  simpa only [sum_integral_actualNoncentralEigenvalue_sq_eq_finite] using
    actualNoncentralMatrixLogDet_low_scale_curvature M

end
end JinWishart
#print axioms JinWishart.eval_noncentralGramSquaredTracePolynomial
#print axioms JinWishart.integral_actualNoncentralGram_squaredTrace
#print axioms JinWishart.sum_integral_actualNoncentralEigenvalue_sq_eq_finite
#print axioms JinWishart.actualNoncentralMatrixLogDet_low_scale_finite_curvature
