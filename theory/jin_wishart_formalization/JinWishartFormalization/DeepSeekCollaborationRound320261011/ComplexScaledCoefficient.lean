import Mathlib.Tactic

theorem deepseek_round3_ComplexScaledCoefficient :
    (abs (((Real.sqrt 2)⁻¹) ^ 2)⁻¹) * (2 * Real.pi)⁻¹ = Real.pi⁻¹ := by
  field_simp [pow_two, mul_assoc]
  <;> ring_nf
  <;> field_simp [pow_two, mul_assoc]
  <;> ring_nf
  <;> norm_num
  <;> field_simp [pow_two, mul_assoc]
  <;> ring_nf
  <;> norm_num
  <;> field_simp [pow_two, mul_assoc]
  <;> ring_nf
  <;> norm_num

#print axioms deepseek_round3_ComplexScaledCoefficient
