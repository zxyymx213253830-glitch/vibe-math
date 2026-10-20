import JinWishartFormalization.CorrelatedGramTraceMoments

/-! Expanded closed correlated second spectral moment, finite trace algebra.
Codex. No additional Gaussian premise. [需人工审查] Inherited model/variance.
-/
open Matrix MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

theorem complex_matrix_trace_square_smul_add {n : ℕ} (c : ℂ)
    (S A : Matrix (Fin n) (Fin n) ℂ) :
    ((c • S+A)^2).trace = c^2*(S^2).trace+2*c*(S*A).trace+(A^2).trace := by
  simp only [pow_two,add_mul,mul_add,smul_mul_assoc,mul_smul_comm,smul_smul,
    Matrix.trace_add,Matrix.trace_smul,smul_eq_mul]
  rw [Matrix.trace_mul_comm A S]
  ring

theorem integral_actualCorrelatedGram_squaredTrace_expanded {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) :
    (∫ z : ComplexSample (m := m) (n := p),
      ((complexGram (complexSampleMatrix z*B+M))^2).trace.re ∂stdGaussian _) =
      (m : ℝ)^2*((complexGram B)^2).trace.re + (m : ℝ)*(complexGram B).trace.re^2 +
      2*(m : ℝ)*(complexGram B*complexGram M).trace.re +
      2*(complexGram B).trace.re*(complexGram M).trace.re + ((complexGram M)^2).trace.re := by
  rw [integral_actualCorrelatedGram_squaredTrace,complex_matrix_trace_square_smul_add]
  norm_num [Complex.add_re,Complex.mul_re,Complex.mul_im,pow_two]
  ring

end
end JinWishart
#print axioms JinWishart.complex_matrix_trace_square_smul_add
#print axioms JinWishart.integral_actualCorrelatedGram_squaredTrace_expanded
