import JinWishartFormalization.ProperGaussianPolynomialLogSquare
import JinWishartFormalization.ActualComplexPolynomialLog

/-! Actual physical holomorphic polynomial/compressed determinant log-square.
Fixed arbitrary complex factors, including zero/singular cases; Real.log0=0.
Codex. [需人工审查] Physical law/variance and map integration. -/
open Matrix MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

theorem integrable_actualComplexMatrix_holomorphic_log_sq (m p : ℕ)
    (P : MvPolynomial (Fin m × Fin p) ℂ) :
    Integrable (fun z=>(Real.log ‖MvPolynomial.eval (complexMatrixEntries z) P‖)^2)
      (stdGaussian (ComplexSample (m := m) (n := p))) := by
  have h := properComplex_pi_polynomial_log_sq_integrable P
  rw [← complexMatrixEntries_law m p] at h
  exact (integrable_map_measure ((MvPolynomial.continuous_eval P).norm.measurable.log.pow_const 2).aestronglyMeasurable
    (measurable_complexMatrixEntries m p).aemeasurable).mp h

theorem integrable_actualAffineCompressedDet_log_sq {m p n q : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (L : Matrix (Fin q) (Fin m) ℂ) (H : Matrix (Fin n) (Fin q) ℂ) :
    Integrable (fun z=>(Real.log ‖(L*(complexSampleMatrix z*B+M)*H).det‖)^2)
      (stdGaussian (ComplexSample (m := m) (n := p))) := by
  simpa only [entryAffineCompressedDet_eval] using
    integrable_actualComplexMatrix_holomorphic_log_sq m p (entryAffineCompressedDet B M L H)

end
end JinWishart
#print axioms JinWishart.integrable_actualComplexMatrix_holomorphic_log_sq
#print axioms JinWishart.integrable_actualAffineCompressedDet_log_sq
