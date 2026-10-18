import JinWishartFormalization.CentralWishartClosedDensity
import Mathlib.Data.Nat.Choose.Basic

/-! Explicit conversion of the finite product coefficient to the conventional
factorial normalization. Codex deterministic proofs, no density assumptions.
-/
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace JinWishart
noncomputable section

theorem centralWishartDensityConstant_eq_factorial (d n : ℕ) :
    centralWishartDensityConstant d n = (Real.pi⁻¹) ^ (n.choose 2) /
      (∏ j : Fin n, ((Nat.factorial (d + j.val) : ℕ) : ℝ)) := by
  induction n with
  | zero => simp [centralWishartDensityConstant]
  | succ n ih =>
      rw [centralWishartDensityConstant_succ, ih, Fin.prod_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, Nat.choose_succ_succ, Nat.choose_one_right,
        pow_add, div_eq_mul_inv, _root_.mul_inv_rev]
      ring

theorem centralWishartDensityConstant_eq_triangular (d n : ℕ) :
    centralWishartDensityConstant d n = (Real.pi⁻¹) ^ (n * (n - 1) / 2) /
      (∏ j : Fin n, ((Nat.factorial (d + j.val) : ℕ) : ℝ)) := by
  rw [centralWishartDensityConstant_eq_factorial, Nat.choose_two_right]

theorem centralWishartDensityConstant_eq_gamma (d n : ℕ) :
    centralWishartDensityConstant d n = (Real.pi⁻¹) ^ (n.choose 2) /
      (∏ j : Fin n, Real.Gamma ((d + j.val + 1 : ℕ) : ℝ)) := by
  rw [centralWishartDensityConstant_eq_factorial]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  simpa only [Nat.cast_add, Nat.cast_one] using (Real.Gamma_nat_eq_factorial (d + j.val)).symm

theorem centralWishartDensityConstant_two : centralWishartDensityConstant 0 2 = Real.pi⁻¹ := by
  norm_num [centralWishartDensityConstant, Fin.prod_univ_two]

end
end JinWishart

#print axioms JinWishart.centralWishartDensityConstant_eq_factorial
#print axioms JinWishart.centralWishartDensityConstant_eq_triangular
#print axioms JinWishart.centralWishartDensityConstant_eq_gamma
#print axioms JinWishart.centralWishartDensityConstant_two
