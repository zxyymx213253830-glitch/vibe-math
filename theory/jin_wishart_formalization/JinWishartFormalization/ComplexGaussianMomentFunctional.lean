import JinWishartFormalization.ComplexGaussianPolynomialMoments
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Gaussian factorial integration as a linear functional

Codex proofs. It is not a ring homomorphism. The associated coefficient map
on univariate polynomials commutes with scalar evaluation.
[需人工审查] Interpretation inherited from the actual product-law integral.
-/
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace JinWishart
noncomputable section

def complexGaussianMomentLinear {ι : Type*} [Fintype ι] :
    MvPolynomial (ι ⊕ ι) ℂ →ₗ[ℂ] ℂ where
  toFun := complexGaussianPolynomialMoment
  map_add' P Q := by
    simp_rw [← integral_complexGaussian_polynomial]
    have he : complexGaussianPolynomialEval (P+Q) =
        fun z => complexGaussianPolynomialEval P z+complexGaussianPolynomialEval Q z := by
      funext z
      exact map_add _ _ _
    rw [he]
    exact integral_add (integrable_complexGaussian_polynomial P)
      (integrable_complexGaussian_polynomial Q)
  map_smul' a P := by
    simp_rw [← integral_complexGaussian_polynomial]
    have he : complexGaussianPolynomialEval (a • P) =
        fun z => a * complexGaussianPolynomialEval P z := by
      funext z
      exact MvPolynomial.eval₂Hom_smul _ _ _ _
    rw [he,integral_const_mul]
    rfl

def complexGaussianIntegratedPolynomial {ι : Type*} [Fintype ι]
    (P : Polynomial (MvPolynomial (ι ⊕ ι) ℂ)) : Polynomial ℂ :=
  ∑ k ∈ P.support, Polynomial.monomial k (complexGaussianPolynomialMoment (P.coeff k))

theorem complexGaussianIntegratedPolynomial_eval {ι : Type*} [Fintype ι]
    (P : Polynomial (MvPolynomial (ι ⊕ ι) ℂ)) (x : ℂ) :
    (complexGaussianIntegratedPolynomial P).eval x =
      complexGaussianPolynomialMoment (P.eval₂ (RingHom.id _) (MvPolynomial.C x)) := by
  classical
  change (complexGaussianIntegratedPolynomial P).eval x = complexGaussianMomentLinear _
  rw [Polynomial.eval₂_eq_sum,Polynomial.sum_def,map_sum]
  unfold complexGaussianIntegratedPolynomial
  simp only [Polynomial.eval_finsetSum,Polynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro k _
  rw [← MvPolynomial.C_pow]
  simp only [RingHom.id_apply]
  rw [show P.coeff k * MvPolynomial.C (x^k) = (x^k) • P.coeff k by
    rw [mul_comm,MvPolynomial.C_mul']]
  rw [complexGaussianMomentLinear.map_smul]
  change complexGaussianPolynomialMoment (P.coeff k) * x^k =
    x^k * complexGaussianPolynomialMoment (P.coeff k)
  ring

end
end JinWishart
#print axioms JinWishart.complexGaussianIntegratedPolynomial_eval
#print axioms JinWishart.complexGaussianMomentLinear
