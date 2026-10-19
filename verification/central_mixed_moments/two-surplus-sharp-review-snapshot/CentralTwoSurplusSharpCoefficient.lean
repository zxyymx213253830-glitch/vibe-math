import JinWishartFormalization.CentralComplementCubic
import JinWishartFormalization.CentralMinimumPolynomialSpecializations
import JinWishartFormalization.CentralMinimumDensityHardEdge
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite

/-! Explicit sharp constant for every central (N+2) by N complex sample, N>0.
Codex. The complement polynomial is identified with the already proved actual
CDF polynomial; no density or target asymptotic is assumed.
[需人工审查] Inherited actual-law, variance and measure interpretation.
-/
open Filter
open scoped Topology
namespace JinWishart
noncomputable section

theorem centralMinimumRealPolynomial_two_surplus_normalized (N : ℕ) (hN : 0 < N) :
    Polynomial.C (centralDeterminantPowerMoment 0 N 2)⁻¹ *
      centralMinimumRealPolynomial 2 N = centralComplementMinorPolynomial N := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Ici_infinite (0 : ℝ)).mono
  intro x hx
  simp only [Set.mem_ofPred_eq,Polynomial.eval_mul,Polynomial.eval_C]
  rw [← centralRectangularMinimumPolynomial_eq_realPolynomial,
    centralRectangularMinimumPolynomial_two_surplus N hN x hx,
    twoExtraRowMinimumPolynomial_eq_complement]

theorem centralMinimumRealPolynomial_two_surplus_coeff (N : ℕ) (hN : 0 < N) (k : ℕ) :
    (centralDeterminantPowerMoment 0 N 2)⁻¹ *
      (centralMinimumRealPolynomial 2 N).coeff k =
      (centralComplementMinorPolynomial N).coeff k := by
  have h := congrArg (fun p : Polynomial ℝ => p.coeff k)
    (centralMinimumRealPolynomial_two_surplus_normalized N hN)
  simpa only [Polynomial.coeff_C_mul] using h

theorem centralMinimumFiniteHardEdgeCoefficient_two_surplus (n : ℕ) :
    centralMinimumFiniteHardEdgeCoefficient 2 n =
      ((n+1 : ℕ) : ℝ)*(((n+1 : ℕ) : ℝ)+1)*(((n+1 : ℕ) : ℝ)+2)/36 := by
  have hc := centralMinimumRealPolynomial_two_surplus_coeff (n+1) (by omega)
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  rw [centralComplementMinorPolynomial_coeff_zero] at h0
  rw [centralComplementMinorPolynomial_coeff_one] at h1
  rw [centralComplementMinorPolynomial_coeff_two] at h2
  rw [centralComplementMinorPolynomial_coeff_three] at h3
  unfold centralMinimumFiniteHardEdgeCoefficient
  norm_num [Finset.sum_range_succ]
  push_cast at h0 h1 h2 h3 ⊢
  linear_combination -h3 + ((n : ℝ)+1)*h2 -
    ((n : ℝ)+1)^2/2*h1 + ((n : ℝ)+1)^3/6*h0

theorem actualCentralMinimumCDF_two_surplus_sharp_limit (n : ℕ) :
    Tendsto (fun x => actualCentralMinimumCDF 2 n x/x^3) (𝓝[>] 0)
      (𝓝 (((n+1 : ℕ) : ℝ)*(((n+1 : ℕ) : ℝ)+1)*(((n+1 : ℕ) : ℝ)+2)/36)) := by
  simpa only [centralMinimumFiniteHardEdgeCoefficient_two_surplus] using
    actualCentralMinimumCDF_finite_sharp_coefficient_limit 2 n

theorem centralMinimumPDFCore_two_surplus_sharp_limit (n : ℕ) :
    Tendsto (fun x => centralMinimumPDFCore 2 n x/x^2) (𝓝[>] 0)
      (𝓝 (((n+1 : ℕ) : ℝ)*(((n+1 : ℕ) : ℝ)+1)*(((n+1 : ℕ) : ℝ)+2)/12)) := by
  have h := centralMinimumPDFCore_sharp_coefficient_limit 2 n
  rw [centralMinimumFiniteHardEdgeCoefficient_two_surplus] at h
  convert h using 1 <;> norm_num <;> ring

end
end JinWishart
#print axioms JinWishart.centralMinimumRealPolynomial_two_surplus_normalized
#print axioms JinWishart.centralMinimumRealPolynomial_two_surplus_coeff
#print axioms JinWishart.centralMinimumFiniteHardEdgeCoefficient_two_surplus
#print axioms JinWishart.actualCentralMinimumCDF_two_surplus_sharp_limit
#print axioms JinWishart.centralMinimumPDFCore_two_surplus_sharp_limit
