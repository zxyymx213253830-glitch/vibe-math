import JinWishartFormalization.CentralRectangularMinimumPolynomial
import JinWishartFormalization.RectangularWishartTwoExtraRows
import JinWishartFormalization.RectangularWishartOneExtraRow

/-! Consistency of the universal factorial functional with earlier fast formulas.
Codex proofs via equal actual laws; no candidate-density premise.
[需人工审查] Inherited actual-law interpretation.
-/
namespace JinWishart
noncomputable section

theorem centralRectangularMinimumPolynomial_zero_surplus (n : ℕ) (hn : 0 < n)
    (x : ℝ) (hx : 0 ≤ x) : centralRectangularMinimumPolynomial 0 n x = 1 := by
  have h := actualCentralRectangular_minimum_CDF 0 n hn x hx
  rw [show 0+n=n by omega] at h
  simp only [centralGaussianSampleMinimum] at h
  have hs := actualCentralSquare_minimum_CDF n hn x hx
  simp only [centralSquareSampleMinimum] at hs
  have he := Real.exp_pos (-(n : ℝ)*x)
  apply mul_left_cancel₀ he.ne'
  have hh := h.symm.trans hs
  linarith only [hh]

theorem centralRectangularMinimumPolynomial_one_surplus (n : ℕ) (hn : 0 < n)
    (x : ℝ) (hx : 0 ≤ x) :
    centralRectangularMinimumPolynomial 1 n x = oneExtraRowMinimumPolynomial n x := by
  have h := actualCentralRectangular_minimum_CDF 1 n hn x hx
  rw [show 1+n=n+1 by omega] at h
  simp only [centralGaussianSampleMinimum] at h
  have hs := actualOneExtraRow_minimum_CDF n hn x hx
  simp only [oneExtraRowSampleMinimum] at hs
  have he := Real.exp_pos (-(n : ℝ)*x)
  nlinarith

theorem centralRectangularMinimumPolynomial_two_surplus (n : ℕ) (hn : 0 < n)
    (x : ℝ) (hx : 0 ≤ x) :
    centralRectangularMinimumPolynomial 2 n x = twoExtraRowMinimumPolynomial n x := by
  have h := actualCentralRectangular_minimum_CDF 2 n hn x hx
  rw [show 2+n=n+2 by omega] at h
  have hs := actualTwoExtraRows_minimum_CDF n hn x hx
  have he := Real.exp_pos (-(n : ℝ)*x)
  nlinarith

end
end JinWishart
#print axioms JinWishart.centralRectangularMinimumPolynomial_zero_surplus
#print axioms JinWishart.centralRectangularMinimumPolynomial_one_surplus
#print axioms JinWishart.centralRectangularMinimumPolynomial_two_surplus
