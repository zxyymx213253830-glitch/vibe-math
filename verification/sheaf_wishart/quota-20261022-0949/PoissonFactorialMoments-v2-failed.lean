import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! Codex. Seed2026102603 controls precede source. Algebraic exponential-series
moments, including signed real arguments. No probability-law assertion here. -/
open Finset
namespace JinWishart
noncomputable section

def poissonFactorialMomentPolynomial (q k : ℕ) (x : ℝ) : ℝ :=
  (k.factorial : ℝ) * ∑ j ∈ range (k+1), ((q+k).choose (k-j) : ℝ) * x^j/(j.factorial : ℝ)

private theorem exponential_hasSum (x : ℝ) :
    HasSum (fun n : ℕ => x^n/(n.factorial : ℝ)) (Real.exp x) := by
  have ht : (∑' n : ℕ, x^n/(n.factorial : ℝ)) = Real.exp x := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
    apply tsum_congr
    intro n
    simp [div_eq_mul_inv, smul_eq_mul, mul_comm]
  rw [← ht]
  exact (Real.summable_pow_div_factorial x).hasSum

theorem poisson_choose_hasSum (x : ℝ) (j : ℕ) :
    HasSum (fun n : ℕ => x^n/(n.factorial : ℝ)*(n.choose j : ℝ))
      (x^j/(j.factorial : ℝ)*Real.exp x) := by
  have he (n : ℕ) :
      x^(n+j)/((n+j).factorial : ℝ)*((n+j).choose j : ℝ) =
        (x^j/(j.factorial : ℝ))*(x^n/(n.factorial : ℝ)) := by
    have hc : ((n+j).choose j : ℝ)*(n.factorial : ℝ)*(j.factorial : ℝ) =
        ((n+j).factorial : ℝ) := by
      exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial n j
    have hn : (n.factorial : ℝ) ≠ 0 := by positivity
    have hj : (j.factorial : ℝ) ≠ 0 := by positivity
    have hnj : ((n+j).factorial : ℝ) ≠ 0 := by positivity
    rw [pow_add]
    field_simp [hn, hj, hnj]
    linear_combination (x^n*x^j)*hc
  have hs : HasSum (fun n : ℕ =>
      x^(n+j)/((n+j).factorial : ℝ)*((n+j).choose j : ℝ))
      (x^j/(j.factorial : ℝ)*Real.exp x) := by
    simpa only [he] using (exponential_hasSum x).mul_left (x^j/(j.factorial : ℝ))
  have hz : ∑ n ∈ range j, x^n/(n.factorial : ℝ)*(n.choose j : ℝ) = 0 := by
    apply sum_eq_zero
    intro n hn
    rw [Nat.choose_eq_zero_of_lt (mem_range.mp hn), Nat.cast_zero, mul_zero]
  simpa only [hz, zero_add] using hs.sum_range_add

theorem factorial_ratio_vandermonde (q k n : ℕ) :
    ((n+q+k).factorial : ℝ)/((n+q).factorial : ℝ) =
      (k.factorial : ℝ) * ∑ j ∈ range (k+1),
        ((q+k).choose (k-j) : ℝ)*(n.choose j : ℝ) := by
  have hc : ((n+q+k).choose k : ℝ)*(k.factorial : ℝ)*((n+q).factorial : ℝ) =
      ((n+q+k).factorial : ℝ) := by
    have h := Nat.choose_mul_factorial_mul_factorial (show k ≤ n+q+k by omega)
    simp only [Nat.add_sub_cancel] at h
    exact_mod_cast h
  have hv : ((n+q+k).choose k : ℝ) =
      ∑ j ∈ range (k+1), ((q+k).choose (k-j) : ℝ)*(n.choose j : ℝ) := by
    have h := Nat.add_choose_eq n (q+k) k
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
    have hn : (n+q+k).choose k =
        ∑ j ∈ range (k+1), (q+k).choose (k-j)*n.choose j := by
      simpa only [Nat.add_assoc, Nat.mul_comm] using h
    exact_mod_cast hn
  apply (div_eq_iff (by positivity : ((n+q).factorial : ℝ) ≠ 0)).mpr
  rw [← hc, hv]
  ring

theorem poisson_factorialMoment_hasSum (q k : ℕ) (x : ℝ) :
    HasSum (fun n : ℕ => (x^n/(n.factorial : ℝ))*
      (((n+q+k).factorial : ℝ)/((n+q).factorial : ℝ)))
      (Real.exp x * poissonFactorialMomentPolynomial q k x) := by
  have hs := (hasSum_sum (s := range (k+1)) (fun j _ =>
    (poisson_choose_hasSum x j).mul_left ((q+k).choose (k-j) : ℝ))).mul_left
      (k.factorial : ℝ)
  convert hs using 1
  · funext n
    rw [factorial_ratio_vandermonde]
    simp only [mul_sum]
    apply sum_congr rfl
    intro j _
    ring
  · unfold poissonFactorialMomentPolynomial
    simp only [mul_sum]
    apply sum_congr rfl
    intro j _
    ring

end
end JinWishart
#print axioms JinWishart.poisson_choose_hasSum
#print axioms JinWishart.factorial_ratio_vandermonde
#print axioms JinWishart.poisson_factorialMoment_hasSum
