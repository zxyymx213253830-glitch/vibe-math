import JinWishartFormalization.GammaFactorialMoment
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.Degree.Operations

/-! Codex. Seed2026102404 exact controls before source.
Deterministic factorial-moment orthogonality, not a new stochastic law.
[需人工审查] Sign/normalization in later original-T1 use. -/
open Polynomial
namespace JinWishart
noncomputable section

def factorialLaguerre (n : ℕ) : ℂ[X] :=
  ∑ k ∈ Finset.range (n+1), C (((-1 : ℂ)^(n-k))*(n.factorial : ℂ)*
    (n.choose k : ℂ)/(k.factorial : ℂ))*X^k

private theorem alternatingPolynomialSum (n : ℕ) (p : ℂ[X]) (hp : p.natDegree<n) :
    (∑ k ∈ Finset.range (n+1),(-1 : ℂ)^(n-k)*(n.choose k : ℂ)*p.eval ((k : ℂ)+1))=0 := by
  have h := congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hp) (1 : ℂ)
  rw [fwdDiff_iter_eq_sum_shift] at h
  simpa [zsmul_eq_mul,Int.cast_mul,Int.cast_pow,Int.cast_neg,Int.cast_one,
    Nat.cast_smul_eq_nsmul,add_comm] using h

theorem factorial_alternating_moment_sum (n j : ℕ) (hj : j<n) :
    (∑ k ∈ Finset.range (n+1),(-1 : ℂ)^(n-k)*(n.choose k : ℂ)*
      ((j+k).factorial : ℂ)/(k.factorial : ℂ))=0 := by
  have h := alternatingPolynomialSum n (ascPochhammer ℂ j) (by simpa using hj)
  have hr (k : ℕ) : ((j+k).factorial : ℂ)/(k.factorial : ℂ)=
      (ascPochhammer ℂ j).eval ((k : ℂ)+1) := by
    apply (div_eq_iff (by exact_mod_cast Nat.factorial_ne_zero k : (k.factorial : ℂ)≠0)).2
    simpa [Nat.add_comm,mul_comm] using (factorial_mul_ascPochhammer ℂ k j).symm
  calc
    _ = ∑ k ∈ Finset.range (n+1),(-1 : ℂ)^(n-k)*(n.choose k : ℂ)*
        (ascPochhammer ℂ j).eval ((k : ℂ)+1) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [mul_div_assoc,hr]
    _ = 0 := h

private theorem factorialLaguerre_degree_le (n : ℕ) : (factorialLaguerre n).natDegree≤n := by
  unfold factorialLaguerre
  apply natDegree_sum_le_of_forall_le
  intro k hk
  exact (natDegree_C_mul_X_pow_le _ _).trans (by simpa using (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))

private theorem factorialLaguerre_coeff_top (n : ℕ) : (factorialLaguerre n).coeff n=1 := by
  unfold factorialLaguerre
  simp [coeff_sum,coeff_C_mul_X_pow,Finset.sum_eq_single n,Nat.factorial_ne_zero]

theorem factorialLaguerre_monic (n : ℕ) : (factorialLaguerre n).Monic := by
  exact monic_of_natDegree_le_of_coeff_eq_one n (factorialLaguerre_degree_le n)
    (factorialLaguerre_coeff_top n)

theorem factorialLaguerre_natDegree (n : ℕ) : (factorialLaguerre n).natDegree=n := by
  apply le_antisymm (factorialLaguerre_degree_le n)
  exact le_natDegree_of_ne_zero (by rw [factorialLaguerre_coeff_top];norm_num)

theorem factorialLaguerre_moment_orthogonal (n j : ℕ) (hj : j<n) :
    factorialMomentFunctional ((X : ℂ[X])^j*factorialLaguerre n)=0 := by
  unfold factorialLaguerre
  simp only [Finset.mul_sum,map_sum]
  have he (k : ℕ) : factorialMomentFunctional
      ((X : ℂ[X])^j*(C (((-1 : ℂ)^(n-k))*(n.factorial : ℂ)*(n.choose k : ℂ)/(k.factorial : ℂ))*X^k)) =
      (n.factorial : ℂ)*((-1 : ℂ)^(n-k)*(n.choose k : ℂ)*((j+k).factorial : ℂ)/(k.factorial : ℂ)) := by
    rw [show (X : ℂ[X])^j*(C (((-1 : ℂ)^(n-k))*(n.factorial : ℂ)*(n.choose k : ℂ)/(k.factorial : ℂ))*X^k)=
      (((-1 : ℂ)^(n-k))*(n.factorial : ℂ)*(n.choose k : ℂ)/(k.factorial : ℂ)) • X^(j+k) by
      simp only [smul_eq_C_mul,pow_add];ring]
    rw [map_smul,factorialMoment_X_pow]
    simp only [RingHom.id_apply,smul_eq_mul]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum,factorial_alternating_moment_sum n j hj,mul_zero]

theorem factorialLaguerre_eval_neg (n : ℕ) (x : ℂ) :
    (-1 : ℂ)^n*(factorialLaguerre n).eval (-x)=
      (n.factorial : ℂ)*∑ k ∈ Finset.range (n+1),(n.choose k : ℂ)*x^k/(k.factorial : ℂ) := by
  unfold factorialLaguerre
  simp only [eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k≤n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hs : (-1 : ℂ)^n*((-1 : ℂ)^(n-k)*(-1)^k)=1 := by
    rw [← pow_add,Nat.sub_add_cancel hkn,←pow_two,←pow_mul]
    simp
  rw [neg_pow]
  calc
    _ = ((-1 : ℂ)^n*((-1 : ℂ)^(n-k)*(-1)^k))*
        ((n.factorial : ℂ)*(n.choose k : ℂ)*x^k/(k.factorial : ℂ)) := by ring
    _ = _ := by rw [hs];ring

end
end JinWishart
#print axioms JinWishart.factorial_alternating_moment_sum
#print axioms JinWishart.factorialLaguerre_monic
#print axioms JinWishart.factorialLaguerre_natDegree
#print axioms JinWishart.factorialLaguerre_moment_orthogonal
#print axioms JinWishart.factorialLaguerre_eval_neg
