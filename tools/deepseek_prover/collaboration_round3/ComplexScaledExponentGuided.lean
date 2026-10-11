import Mathlib.Tactic

theorem deepseek_round3_ComplexScaledExponent :
    ∀ z : ℂ, -‖((Real.sqrt 2)⁻¹)⁻¹ • z‖ ^ 2 / 2 = -‖z‖ ^ 2 := by
  intro z
  rw [inv_inv, deepseek_round3_ComplexScaledNormSquare]
  sorry
