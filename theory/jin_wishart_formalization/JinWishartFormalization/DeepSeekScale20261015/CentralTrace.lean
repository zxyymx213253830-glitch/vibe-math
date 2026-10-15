import JinWishartFormalization.WishartProbability
open Matrix
theorem deepseek_central_trace_shift (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (x : ℝ) :
    (A + (x : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).trace.re =
      A.trace.re + (n : ℝ) * x := by
  have h1 : (A + (x : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).trace.re = A.trace.re + (n : ℝ) * x := by
    simp [Matrix.trace, Matrix.mul_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.mul_sum, mul_add, add_mul, mul_comm, mul_assoc]
    <;>
    simp_all [Complex.ext_iff, Complex.re, Complex.im, Complex.ofReal_re, Complex.ofReal_im]
    <;>
    ring_nf
    <;>
    field_simp [Complex.ext_iff, Complex.re, Complex.im, Complex.ofReal_re, Complex.ofReal_im]
    <;>
    ring_nf
    <;>
    norm_cast
    <;>
    simp_all [Complex.ext_iff, Complex.re, Complex.im, Complex.ofReal_re, Complex.ofReal_im]
    <;>
    ring_nf
    <;>
    norm_cast
    <;>
    linarith
  exact h1

#print axioms deepseek_central_trace_shift
