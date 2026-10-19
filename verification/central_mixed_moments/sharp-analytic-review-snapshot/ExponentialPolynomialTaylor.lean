import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Finite coefficient arithmetic for exponential-polynomial Taylor values.
Codex deterministic calculus; no probability/density assumption. -/
open Polynomial
namespace JinWishart
noncomputable section

theorem iteratedDeriv_polynomial_eval (P : Polynomial ℝ) (k : ℕ) (x : ℝ) :
    iteratedDeriv k (fun t => P.eval t) x = ((Polynomial.derivative^[k]) P).eval x := by
  induction k generalizing P with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ']
    have he : deriv (fun t => P.eval t) = (fun t => P.derivative.eval t) :=
      funext (fun t => P.deriv)
    rw [he,ih,Function.iterate_succ_apply]

theorem iteratedDeriv_polynomial_eval_zero (P : Polynomial ℝ) (k : ℕ) :
    iteratedDeriv k (fun t => P.eval t) 0 = (k.factorial : ℝ)*P.coeff k := by
  rw [iteratedDeriv_polynomial_eval,← Polynomial.coeff_zero_eq_eval_zero,Polynomial.coeff_iterate_derivative]
  simp only [zero_add,Nat.descFactorial_self,nsmul_eq_mul]

theorem iteratedDeriv_exp_mul_polynomial_zero (P : Polynomial ℝ) (c : ℝ) (k : ℕ) :
    iteratedDeriv k (fun x => Real.exp (c*x)*P.eval x) 0 =
      ∑ i ∈ Finset.range (k+1), (k.choose i : ℝ)*c^i*((k-i).factorial : ℝ)*P.coeff (k-i) := by
  have he : ContDiffAt ℝ k (fun x : ℝ => Real.exp (c*x)) 0 := by fun_prop
  have hp : ContDiffAt ℝ k (fun x : ℝ => P.eval x) 0 :=
    (AnalyticOnNhd.eval_polynomial (𝕜 := ℝ) P 0 (Set.mem_univ 0)).contDiffAt
  rw [iteratedDeriv_fun_mul he hp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [iteratedDeriv_exp_const_mul,iteratedDeriv_polynomial_eval_zero]
  simp only [mul_zero,Real.exp_zero,mul_one]
  ring

end
end JinWishart
#print axioms JinWishart.iteratedDeriv_polynomial_eval
#print axioms JinWishart.iteratedDeriv_polynomial_eval_zero
#print axioms JinWishart.iteratedDeriv_exp_mul_polynomial_zero
