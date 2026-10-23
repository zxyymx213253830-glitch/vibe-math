import JinWishartFormalization.IncompleteGamma
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Derivative

/-! Finite factorial functional identifies upper integer Gamma moments.
Codex. Additional exact recurrence controls run before source, seed2026102246.
No probability density or integral interchange is asserted by this algebra. -/
open Polynomial
namespace JinWishart
noncomputable section

def factorialMomentFunctional : ℂ[X] →ₗ[ℂ] ℂ :=
  Polynomial.lsum (fun k => (LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight (k.factorial : ℂ))

@[simp] private theorem factorialMoment_monomial (k : ℕ) (a : ℂ) :
    factorialMomentFunctional (monomial k a)=a*(k.factorial : ℂ) := by
  simp [factorialMomentFunctional,Polynomial.lsum_apply,Polynomial.sum_monomial_index]

private theorem factorialMoment_eval_derivative (p : ℂ[X]) :
    factorialMomentFunctional p=p.eval 0+factorialMomentFunctional p.derivative := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add,eval_add,derivative_add,hp,hq]
    ring
  | monomial n a =>
    cases n with
    | zero => simp
    | succ n =>
      simp [derivative_monomial,Nat.factorial_succ]
      ring

private theorem factorialMoment_shift_succ (k : ℕ) (x : ℂ) :
    factorialMomentFunctional ((X+C x)^(k+1))=
      x^(k+1)+(k+1 : ℂ)*factorialMomentFunctional ((X+C x)^k) := by
  have h := factorialMoment_eval_derivative ((X+C x)^(k+1))
  simpa only [eval_pow,eval_add,eval_X,eval_C,zero_add,derivative_X_add_C_pow,
    Nat.add_sub_cancel,← smul_eq_C_mul,map_smul,RingHom.id_apply,smul_eq_mul,Nat.cast_add,Nat.cast_one] using h

theorem factorialMoment_X_pow (k : ℕ) :
    factorialMomentFunctional ((X : ℂ[X])^k)=(k.factorial : ℂ) := by
  rw [← monomial_one_right_eq_X_pow,factorialMoment_monomial,one_mul]

theorem upperGammaNat_eq_factorialMoment (k : ℕ) (x : ℝ) (hx : 0≤x) :
    upperGammaNat k x=(Real.exp (-x) : ℂ)*
      factorialMomentFunctional ((X+C (x : ℂ))^k) := by
  induction k with
  | zero => simp [upperGammaNat_zero,← monomial_zero_left]
  | succ k ih =>
    rw [upperGammaNat_succ k hx,ih,factorialMoment_shift_succ]
    have hp : (x : ℂ)^((k+1 : ℕ) : ℂ)=(x : ℂ)^(k+1) := by simp
    rw [hp]
    push_cast
    ring

end
end JinWishart
#print axioms JinWishart.factorialMoment_X_pow
#print axioms JinWishart.upperGammaNat_eq_factorialMoment
