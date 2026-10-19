import JinWishartFormalization.CentralComplementLowCoefficients

/-! Exact low four coefficients, for all dimensions including small ones.
Codex deterministic algebra. No interpolation from numerical examples. -/
namespace JinWishart
noncomputable section

theorem nat_cast_choose_three_real (N : ℕ) :
    (N.choose 3 : ℝ)=(N : ℝ)*((N : ℝ)-1)*((N : ℝ)-2)/6 := by
  cases N with
  | zero => norm_num
  | succ N =>
    cases N with
    | zero => norm_num [Nat.choose]
    | succ N =>
      cases N with
      | zero => norm_num
      | succ N =>
        rw [Nat.cast_choose ℝ (show 3≤N+1+1+1 by omega)]
        rw [show N+1+1+1-3=N by omega]
        simp only [Nat.factorial_succ,Nat.factorial_zero,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
        have h : (N.factorial : ℝ)≠0 := by positivity
        field_simp
        <;> ring

theorem centralComplementMinorPolynomial_coeff_zero (N : ℕ) :
    (centralComplementMinorPolynomial N).coeff 0=1 := by
  rw [centralComplementMinorPolynomial_coeff_bounded]
  norm_num [complementCoefficientTerm,Finset.sum_range_succ]

theorem centralComplementMinorPolynomial_coeff_one (N : ℕ) :
    (centralComplementMinorPolynomial N).coeff 1=(N : ℝ) := by
  rw [centralComplementMinorPolynomial_coeff_bounded]
  norm_num [complementCoefficientTerm,Finset.sum_range_succ]
  ring

theorem centralComplementMinorPolynomial_coeff_two (N : ℕ) :
    (centralComplementMinorPolynomial N).coeff 2=(N : ℝ)^2/2 := by
  rw [centralComplementMinorPolynomial_coeff_bounded]
  cases N with
  | zero => norm_num [complementCoefficientTerm,Finset.sum_range_succ]
  | succ N =>
    norm_num [complementCoefficientTerm,Finset.sum_range_succ,Nat.cast_choose_two]
    ring

theorem centralComplementMinorPolynomial_coeff_three (N : ℕ) :
    (centralComplementMinorPolynomial N).coeff 3=
      (N : ℝ)*((N : ℝ)-1)*(5*(N : ℝ)+2)/36 := by
  rw [centralComplementMinorPolynomial_coeff_bounded]
  cases N with
  | zero => norm_num [complementCoefficientTerm,Finset.sum_range_succ]
  | succ N =>
    cases N with
    | zero => norm_num [complementCoefficientTerm,Finset.sum_range_succ,Nat.choose]
    | succ N =>
      norm_num [complementCoefficientTerm,Finset.sum_range_succ,Nat.cast_choose_two,nat_cast_choose_three_real]
      ring

end
end JinWishart
#print axioms JinWishart.nat_cast_choose_three_real
#print axioms JinWishart.centralComplementMinorPolynomial_coeff_zero
#print axioms JinWishart.centralComplementMinorPolynomial_coeff_one
#print axioms JinWishart.centralComplementMinorPolynomial_coeff_two
#print axioms JinWishart.centralComplementMinorPolynomial_coeff_three
