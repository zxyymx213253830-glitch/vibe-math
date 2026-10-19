import JinWishartFormalization.CentralMinimumPolynomialNormalization

/-!
# Real coefficients for the general central minimum polynomial

Codex algebraic proofs. Complex real-part is linear, not multiplicative;
we apply it to coefficients rather than claiming it is a ring homomorphism.
[需人工审查] Inherited actual minimum-law interpretation.
-/
open scoped BigOperators
namespace JinWishart
noncomputable section

def realCoefficientPolynomial (P : Polynomial ℂ) : Polynomial ℝ :=
  ∑ k ∈ P.support, Polynomial.monomial k (P.coeff k).re

theorem realCoefficientPolynomial_coeff (P : Polynomial ℂ) (k : ℕ) :
    (realCoefficientPolynomial P).coeff k = (P.coeff k).re := by
  classical
  unfold realCoefficientPolynomial
  rw [Polynomial.finsetSum_coeff,Finset.sum_eq_single k]
  · simp
  · intro b _ hbk
    simp [Polynomial.coeff_monomial,hbk]
  · intro hk
    have hz : P.coeff k = 0 := by simpa only [Polynomial.mem_support_iff,not_not] using hk
    simp [hz]

theorem realCoefficientPolynomial_eval (P : Polynomial ℂ) (x : ℝ) :
    (realCoefficientPolynomial P).eval x = (P.eval (x : ℂ)).re := by
  classical
  unfold realCoefficientPolynomial
  rw [Polynomial.eval_finsetSum]
  conv_rhs => rw [Polynomial.eval_eq_sum,Polynomial.sum_def]
  simp only [Polynomial.eval_monomial]
  rw [show (∑ k ∈ P.support, P.coeff k * (x : ℂ)^k).re =
      ∑ k ∈ P.support, (P.coeff k * (x : ℂ)^k).re from
        map_sum Complex.reAddGroupHom _ _]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Complex.ofReal_pow]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]

theorem realCoefficientPolynomial_natDegree_le (P : Polynomial ℂ) :
    (realCoefficientPolynomial P).natDegree ≤ P.natDegree := by
  classical
  unfold realCoefficientPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  exact (Polynomial.natDegree_monomial_le _).trans (Polynomial.le_natDegree_of_mem_supp k hk)

def centralMinimumRealPolynomial (d n : ℕ) : Polynomial ℝ :=
  realCoefficientPolynomial (centralMinimumUnivariatePolynomial d n)

theorem centralMinimumRealPolynomial_coeff_top (d n : ℕ) :
    (centralMinimumRealPolynomial d n).coeff (d*n) = 1 := by
  rw [centralMinimumRealPolynomial,realCoefficientPolynomial_coeff,
    centralMinimumUnivariatePolynomial_coeff_top]
  rfl

theorem centralMinimumRealPolynomial_natDegree (d n : ℕ) :
    (centralMinimumRealPolynomial d n).natDegree = d*n := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    ((realCoefficientPolynomial_natDegree_le _).trans (centralMinimumUnivariatePolynomial_natDegree_le d n))
  change (centralMinimumRealPolynomial d n).coeff (d*n) ≠ 0
  rw [centralMinimumRealPolynomial_coeff_top]
  exact one_ne_zero

theorem centralMinimumRealPolynomial_monic (d n : ℕ) :
    (centralMinimumRealPolynomial d n).Monic := by
  change (centralMinimumRealPolynomial d n).leadingCoeff = 1
  rw [← Polynomial.coeff_natDegree,centralMinimumRealPolynomial_natDegree,
    centralMinimumRealPolynomial_coeff_top]

theorem centralRectangularMinimumPolynomial_eq_realPolynomial (d n : ℕ) (x : ℝ) :
    centralRectangularMinimumPolynomial d n x = (centralDeterminantPowerMoment 0 n d)⁻¹ *
      (centralMinimumRealPolynomial d n).eval x := by
  rw [centralRectangularMinimumPolynomial_eq_univariate]
  rw [centralMinimumRealPolynomial,realCoefficientPolynomial_eval]

end
end JinWishart
#print axioms JinWishart.realCoefficientPolynomial_coeff
#print axioms JinWishart.realCoefficientPolynomial_eval
#print axioms JinWishart.realCoefficientPolynomial_natDegree_le
#print axioms JinWishart.centralMinimumRealPolynomial_coeff_top
#print axioms JinWishart.centralMinimumRealPolynomial_natDegree
#print axioms JinWishart.centralMinimumRealPolynomial_monic
#print axioms JinWishart.centralRectangularMinimumPolynomial_eq_realPolynomial
