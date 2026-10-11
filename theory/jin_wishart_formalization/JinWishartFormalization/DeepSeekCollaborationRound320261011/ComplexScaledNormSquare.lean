import Mathlib.Tactic

theorem deepseek_round3_ComplexScaledNormSquare (z : ℂ) :
    ‖Real.sqrt 2 • z‖ ^ 2 = 2 * ‖z‖ ^ 2 := by
  simp [norm_smul, Real.sqrt_nonneg, mul_pow, mul_assoc]
  <;> field_simp [pow_two]
  <;> ring_nf
  <;> norm_cast
  <;> field_simp [pow_two]
  <;> ring_nf
  <;> norm_cast
  <;> linarith

#print axioms deepseek_round3_ComplexScaledNormSquare
