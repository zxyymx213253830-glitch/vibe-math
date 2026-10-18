import JinWishartFormalization.ComplexGaussianMomentFunctional
import JinWishartFormalization.CentralRectangularMinimumPolynomial

/-! A single fixed univariate coefficient polynomial for the general minimum law.
Codex proofs. No probability integrals in its coefficient definition.
[需人工审查] Inherited actual-law correspondence.
-/
open Matrix
namespace JinWishart
noncomputable section

def shiftedGramPolynomialInX (n d : ℕ) : Polynomial (ComplexMatrixPolynomial n n) :=
  ((gramEntryPolynomial n n).map Polynomial.C +
    (Polynomial.X : Polynomial (ComplexMatrixPolynomial n n)) • 1).det^d

theorem shiftedGramPolynomialInX_eval (n d : ℕ) (x : ℝ) :
    (shiftedGramPolynomialInX n d).eval₂ (RingHom.id _) (MvPolynomial.C (x : ℂ)) =
      shiftedGramDeterminantPolynomial n n d x := by
  classical
  let e := Polynomial.eval₂RingHom (RingHom.id (ComplexMatrixPolynomial n n))
    (MvPolynomial.C (x : ℂ))
  change e (((gramEntryPolynomial n n).map Polynomial.C+
    (Polynomial.X : Polynomial (ComplexMatrixPolynomial n n)) • 1).det^d) = _
  rw [map_pow,e.map_det]
  unfold shiftedGramDeterminantPolynomial
  congr 2
  ext i j
  simp [e,Matrix.map_apply,Matrix.smul_apply,Matrix.one_apply]
  split_ifs <;> simp

def centralMinimumUnivariatePolynomial (d n : ℕ) : Polynomial ℂ :=
  complexGaussianIntegratedPolynomial (shiftedGramPolynomialInX n d)

theorem centralMinimumUnivariatePolynomial_eval (d n : ℕ) (x : ℝ) :
    (centralMinimumUnivariatePolynomial d n).eval (x : ℂ) =
      complexGaussianPolynomialMoment (shiftedGramDeterminantPolynomial n n d x) := by
  rw [centralMinimumUnivariatePolynomial,complexGaussianIntegratedPolynomial_eval,
    shiftedGramPolynomialInX_eval]

theorem centralRectangularMinimumPolynomial_eq_univariate (d n : ℕ) (x : ℝ) :
    centralRectangularMinimumPolynomial d n x = (centralDeterminantPowerMoment 0 n d)⁻¹ *
      ((centralMinimumUnivariatePolynomial d n).eval (x : ℂ)).re := by
  rw [centralMinimumUnivariatePolynomial_eval]
  rfl

end
end JinWishart
#print axioms JinWishart.shiftedGramPolynomialInX_eval
#print axioms JinWishart.centralMinimumUnivariatePolynomial_eval
#print axioms JinWishart.centralRectangularMinimumPolynomial_eq_univariate
