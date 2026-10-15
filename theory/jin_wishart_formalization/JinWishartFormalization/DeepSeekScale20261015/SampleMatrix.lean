import JinWishartFormalization.WishartProbability
open MeasureTheory ProbabilityTheory Matrix
namespace JinWishart
noncomputable section
theorem deepseek_scaled_sampleMatrix (a : ℝ) (z : ComplexSample (m := 2) (n := 2)) :
    complexSampleMatrix (a • z) = (a : ℂ) • complexSampleMatrix z := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [complexSampleMatrix, Complex.ext_iff, smul_eq_mul, mul_add, add_mul]
  <;> ring_nf <;> norm_num <;> aesop
end
end JinWishart

#print axioms JinWishart.deepseek_scaled_sampleMatrix
