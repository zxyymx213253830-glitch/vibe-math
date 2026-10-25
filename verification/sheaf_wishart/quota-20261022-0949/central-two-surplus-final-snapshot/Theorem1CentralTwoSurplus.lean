import JinWishartFormalization.PositiveLaguerreRecurrence
import JinWishartFormalization.TwoSurplusLaguerreSquares
import Mathlib.Algebra.Polynomial.Roots

/-! Codex. Seed2026102506 monic/CD normalization controls precede source;
actual-polynomial controls seed2504 precede source. Formal polynomial chain rule,
not analytic differentiation under an integral.
[需人工审查] Inherited actual model and original-paper normalization mapping. -/
open Polynomial Finset Matrix MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

private theorem monic_laguerre_eval_positive (n : ℕ) (x : ℂ) :
    (factorialLaguerre n).eval (-x)=
      ((-1 : ℂ)^n*(n.factorial : ℂ))*(positiveLaguerrePolynomial n).eval x := by
  have h := factorialLaguerre_eval_neg n x
  have he : (positiveLaguerrePolynomial n).eval x=
      ∑ k ∈ range (n+1),(n.choose k : ℂ)*x^k/(k.factorial : ℂ) := by
    unfold positiveLaguerrePolynomial
    simp only [eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X]
    apply sum_congr rfl
    intro k _
    ring
  rw [← he] at h
  have hs : (-1 : ℂ)^n*(-1)^n=1 := by
    rw [← pow_two,← pow_mul]
    simp
  calc
    _ = ((-1 : ℂ)^n*(-1)^n)*(factorialLaguerre n).eval (-x) := by rw [hs];simp
    _ = (-1 : ℂ)^n*((n.factorial : ℂ)*(positiveLaguerrePolynomial n).eval x) := by rw [mul_assoc,h]
    _ = _ := by ring

private theorem monic_laguerre_derivative_positive (n : ℕ) (x : ℂ) :
    (Polynomial.derivative (factorialLaguerre n)).eval (-x)=
      -(((-1 : ℂ)^n*(n.factorial : ℂ))*(Polynomial.derivative (positiveLaguerrePolynomial n)).eval x) := by
  have hp : (factorialLaguerre n).comp (-X)=
      C ((-1 : ℂ)^n*(n.factorial : ℂ))*positiveLaguerrePolynomial n := by
    apply Polynomial.funext
    intro z
    simp only [eval_comp,eval_neg,eval_X,eval_mul,eval_C]
    exact monic_laguerre_eval_positive n z
  have h := congrArg (fun p : ℂ[X] => (Polynomial.derivative p).eval x) hp
  simp only [derivative_comp,derivative_mul,derivative_C,zero_mul,zero_add,
    derivative_neg,derivative_X,eval_mul,eval_comp,eval_neg,eval_X,eval_one,eval_C] at h
  linear_combination -h

private theorem monic_wronskian_squares (n : ℕ) (x : ℂ) :
    twoSurplusLaguerreWronskian n x =
      (n.factorial : ℂ)*((n+1).factorial : ℂ)*
        ((∑ j ∈ range (n+1),((positiveLaguerrePolynomial j).eval x)^2)/((n+1 : ℕ) : ℂ)) := by
  have hs : (-1 : ℂ)^n*(-1)^(n+1) = -1 := by
    rw [← pow_add,show n+(n+1)=2*n+1 by omega,pow_add,pow_mul]
    norm_num
  have hc := positiveLaguerre_christoffelDarboux n x
  have hn : ((n+1 : ℕ) : ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero n
  have he :
      (positiveLaguerrePolynomial n).eval x*(Polynomial.derivative (positiveLaguerrePolynomial (n+1))).eval x-
      (positiveLaguerrePolynomial (n+1)).eval x*(Polynomial.derivative (positiveLaguerrePolynomial n)).eval x =
        (∑ j ∈ range (n+1),((positiveLaguerrePolynomial j).eval x)^2)/((n+1 : ℕ) : ℂ) := by
    apply (eq_div_iff hn).2
    simpa only [mul_comm] using hc
  unfold twoSurplusLaguerreWronskian
  rw [monic_laguerre_eval_positive,monic_laguerre_eval_positive,
    monic_laguerre_derivative_positive,monic_laguerre_derivative_positive]
  calc
    _ = -((-1 : ℂ)^n*(-1)^(n+1))*(n.factorial : ℂ)*((n+1).factorial : ℂ)*
        ((positiveLaguerrePolynomial n).eval x*(Polynomial.derivative (positiveLaguerrePolynomial (n+1))).eval x-
        (positiveLaguerrePolynomial (n+1)).eval x*(Polynomial.derivative (positiveLaguerrePolynomial n)).eval x) := by ring
    _ = _ := by rw [hs,he];ring

theorem twoSurplusLaguerreWronskian_eq_actualPolynomial (n : ℕ) (x : ℝ) :
    twoSurplusLaguerreWronskian n (x : ℂ) =
      (((n.factorial : ℝ)*((n+1).factorial : ℝ)*twoExtraRowMinimumPolynomial n x : ℝ) : ℂ) := by
  rw [monic_wronskian_squares,twoExtraRowMinimumPolynomial_eq_meanSquares]
  simp_rw [positiveLaguerre_eval_real]
  push_cast
  ring

theorem theorem1CentralTwoSurplus_candidate_eq_polynomial (n : ℕ) (x : ℝ) (hx : 0≤x) :
    theorem1CdfCandidate n (n+2) 0 (by omega) (Nat.zero_le n)
      (fun j : Fin 0 => Fin.elim0 j) x =
        1-Real.exp (-(n : ℝ)*x)*twoExtraRowMinimumPolynomial n x := by
  let D : ℂ := (∏ i : Fin n,(i.val.factorial : ℂ)^2)*(n.factorial : ℂ)*((n+1).factorial : ℂ)
  have hD : D≠0 := by
    dsimp only [D]
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply prod_ne_zero_iff.mpr
        intro i _
        exact pow_ne_zero 2 (by exact_mod_cast Nat.factorial_ne_zero i.val)
      · exact_mod_cast Nat.factorial_ne_zero n
    · exact_mod_cast Nat.factorial_ne_zero (n+1)
  have hDN := norm_ne_zero_iff.mpr hD
  have hP0 : twoExtraRowMinimumPolynomial n 0=1 := by
    have hA (k : ℕ) : oneExtraRowMinimumPolynomial k 0=1 := by
      unfold oneExtraRowMinimumPolynomial
      rw [sum_range_succ']
      simp
    rw [twoExtraRowMinimumPolynomial_eq_meanSquares]
    simp [hA]
    positivity
  have hForm (y : ℝ) (hy : 0≤y) :
      (theorem1PsiMatrix n (n+2) 0 (by omega) (Nat.zero_le n)
        (fun j : Fin 0 => Fin.elim0 j) y).det =
          (Real.exp (-(n : ℝ)*y) : ℂ)*D*(twoExtraRowMinimumPolynomial n y : ℂ) := by
    rw [theorem1CentralTwoSurplus_PsiDet_wronskian n y hy,twoSurplusLaguerreWronskian_eq_actualPolynomial]
    push_cast
    dsimp only [D]
    ring
  rw [theorem1CdfCandidate,hForm x hx,hForm 0 (by norm_num),hP0]
  simp only [mul_zero,neg_zero,Real.exp_zero,Complex.ofReal_one,one_mul,mul_one]
  rw [norm_mul,norm_mul,Complex.norm_of_nonneg (Real.exp_nonneg _),
    Complex.norm_of_nonneg (twoExtraRowMinimumPolynomial_nonneg n x hx)]
  field_simp
  <;> ring

theorem theorem1CentralTwoSurplus_candidate_eq_actualCDF (n : ℕ) (hn : 0<n) (x : ℝ) (hx : 0≤x) :
    theorem1CdfCandidate n (n+2) 0 (by omega) (Nat.zero_le n)
      (fun j : Fin 0 => Fin.elim0 j) x =
        ((stdGaussian (ComplexSample (m := n+2) (n := n)))
          {z | centralGaussianSampleMinimum (n+2) n hn z≤x}).toReal := by
  rw [theorem1CentralTwoSurplus_candidate_eq_polynomial n x hx,
    actualTwoExtraRows_minimum_CDF n hn x hx]

end
end JinWishart
#print axioms JinWishart.twoSurplusLaguerreWronskian_eq_actualPolynomial
#print axioms JinWishart.theorem1CentralTwoSurplus_candidate_eq_polynomial
#print axioms JinWishart.theorem1CentralTwoSurplus_candidate_eq_actualCDF
