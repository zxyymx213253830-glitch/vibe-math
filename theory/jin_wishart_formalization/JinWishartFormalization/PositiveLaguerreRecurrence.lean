import JinWishartFormalization.TwoSurplusGammaWronskian
import Mathlib.Algebra.Polynomial.Derivative

/-! Codex. Seed2026102506 exact coefficient/recurrence controls precede source.
Positive-argument finite Laguerre polynomial and formal confluent CD identity.
No analytic differentiation or probability claim. -/
open Polynomial Finset
namespace JinWishart
noncomputable section

def positiveLaguerrePolynomial (n : ℕ) : ℂ[X] :=
  ∑ k ∈ range (n+1),C ((n.choose k : ℂ)/(k.factorial : ℂ))*X^k

private theorem positiveLaguerre_coeff (n k : ℕ) :
    (positiveLaguerrePolynomial n).coeff k=(n.choose k : ℂ)/(k.factorial : ℂ) := by
  unfold positiveLaguerrePolynomial
  simp only [finsetSum_coeff,coeff_C_mul_X_pow]
  rw [sum_eq_single k]
  · simp
  · intro b _ hb
    simp [hb,Ne.symm hb]
  · intro hk
    have hn : n<k := by simpa [mem_range] using hk
    simp [Nat.choose_eq_zero_of_lt hn]

private theorem positiveLaguerre_choose_recurrence (n k : ℕ) :
    ((n+2 : ℕ) : ℂ)*((n+2).choose (k+1) : ℂ) =
      ((k+1 : ℕ) : ℂ)*((n+1).choose k : ℂ)+
      (2*(n : ℂ)+3)*((n+1).choose (k+1) : ℂ)-
      ((n+1 : ℕ) : ℂ)*(n.choose (k+1) : ℂ) := by
  by_cases hk : k≤n
  · have ht : (n.choose (k+1) : ℂ)*((n+1 : ℕ) : ℂ)=
        ((n+1).choose (k+1) : ℂ)*((n-k : ℕ) : ℂ) := by
      exact_mod_cast (by simpa using Nat.choose_mul_succ_eq n (k+1))
    have hs : ((n+1).choose (k+1) : ℂ)*((k+1 : ℕ) : ℂ)=
        ((n+1).choose k : ℂ)*((n+1-k : ℕ) : ℂ) := by
      exact_mod_cast Nat.choose_succ_right_eq (n+1) k
    have hp : ((n+2).choose (k+1) : ℂ)=
        ((n+1).choose k : ℂ)+((n+1).choose (k+1) : ℂ) := by
      exact_mod_cast (by simpa [Nat.add_assoc] using Nat.choose_succ_succ (n+1) k)
    rw [Nat.cast_sub hk] at ht
    rw [Nat.cast_sub (by omega : k≤n+1)] at hs
    push_cast at ht hs ⊢
    linear_combination ((n : ℂ)+2)*hp-hs+ht
  · by_cases hk1 : k=n+1
    · subst k
      have hz : n.choose (n+1+1)=0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [hz]
      <;> ring
    · have h0 : n.choose (k+1)=0 := Nat.choose_eq_zero_of_lt (by omega)
      have h1 : (n+1).choose k=0 := Nat.choose_eq_zero_of_lt (by omega)
      have h2 : (n+1).choose (k+1)=0 := Nat.choose_eq_zero_of_lt (by omega)
      have h3 : (n+2).choose (k+1)=0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [h0,h1,h2,h3]

theorem positiveLaguerre_recurrence (n : ℕ) :
    ((n+2 : ℕ) : ℂ) • positiveLaguerrePolynomial (n+2) =
      (X+C (2*(n : ℂ)+3))*positiveLaguerrePolynomial (n+1)-
        ((n+1 : ℕ) : ℂ) • positiveLaguerrePolynomial n := by
  ext k
  cases k with
  | zero =>
    simp only [coeff_smul,smul_eq_mul,coeff_sub,add_mul,coeff_add,coeff_X_mul_zero,coeff_C_mul,
      positiveLaguerre_coeff,Nat.choose_zero_right,Nat.factorial_zero,Nat.cast_one,div_one,zero_add,mul_one]
    push_cast
    ring
  | succ k =>
    simp only [coeff_smul,smul_eq_mul,coeff_sub,add_mul,coeff_add,coeff_X_mul,coeff_C_mul,
      positiveLaguerre_coeff]
    rw [Nat.factorial_succ]
    push_cast
    have hf : (k.factorial : ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hk : (k : ℂ)+1≠0 := by exact_mod_cast Nat.succ_ne_zero k
    field_simp
    have h := positiveLaguerre_choose_recurrence n k
    push_cast at h
    linear_combination h

theorem positiveLaguerre_christoffelDarboux (n : ℕ) (x : ℂ) :
    ((n+1 : ℕ) : ℂ)*
      ((positiveLaguerrePolynomial n).eval x*(Polynomial.derivative (positiveLaguerrePolynomial (n+1))).eval x-
        (positiveLaguerrePolynomial (n+1)).eval x*(Polynomial.derivative (positiveLaguerrePolynomial n)).eval x) =
      ∑ j ∈ range (n+1),((positiveLaguerrePolynomial j).eval x)^2 := by
  induction n with
  | zero =>
    norm_num [positiveLaguerrePolynomial,Finset.sum_range_succ]
  | succ n ih =>
    have hr := congrArg (fun p : ℂ[X] => p.eval x) (positiveLaguerre_recurrence n)
    have hd := congrArg (fun p : ℂ[X] => (Polynomial.derivative p).eval x) (positiveLaguerre_recurrence n)
    simp only [eval_smul,smul_eq_mul,eval_sub,eval_mul,eval_add,eval_X,eval_C] at hr
    simp only [map_smul,derivative_sub,derivative_mul,derivative_add,derivative_X,derivative_C,
      add_zero,eval_sub,eval_add,eval_mul,eval_X,eval_C,eval_one,one_mul,eval_smul,smul_eq_mul] at hd
    rw [sum_range_succ]
    push_cast at hr hd ih ⊢
    linear_combination (positiveLaguerrePolynomial (n+1)).eval x*hd-
      (Polynomial.derivative (positiveLaguerrePolynomial (n+1))).eval x*hr+ih

theorem positiveLaguerre_eval_real (n : ℕ) (x : ℝ) :
    (positiveLaguerrePolynomial n).eval (x : ℂ)=(oneExtraRowMinimumPolynomial n x : ℂ) := by
  unfold positiveLaguerrePolynomial oneExtraRowMinimumPolynomial
  simp only [eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X]
  push_cast
  apply sum_congr rfl
  intro k _
  ring

end
end JinWishart
#print axioms JinWishart.positiveLaguerre_recurrence
#print axioms JinWishart.positiveLaguerre_christoffelDarboux
#print axioms JinWishart.positiveLaguerre_eval_real
