import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-! Deterministic denominator algebra for central square Theorem1.
Codex. Seed2026102246:159 exact finite controls precede source.
All sizes including0 for algebra only; no minimum eigenvalue at dimension0. -/
open Matrix
namespace JinWishart
noncomputable section

theorem binomial_overlap_sum_fin (n : ℕ) (i j : Fin n) :
    (∑ k : Fin n,i.val.choose k.val*j.val.choose k.val)=(i.val+j.val).choose j.val := by
  classical
  rw [Fin.sum_univ_eq_sum_range]
  have h := Nat.add_choose_eq i.val j.val j.val
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  have ht : (∑ k ∈ Finset.range (j.val+1),i.val.choose k*j.val.choose k)=
      ∑ k ∈ Finset.range n,i.val.choose k*j.val.choose k := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro k hk hnot
    have hjk : j.val<k := by simp only [Finset.mem_range] at hnot;omega
    rw [Nat.choose_eq_zero_of_lt hjk,mul_zero]
  rw [← ht, h]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.choose_symm (by simpa only [Finset.mem_range_succ_iff] using hk)]

def factorialHankel (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => ((i.val+j.val).factorial : ℂ)

def factorialPascalFactor (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (i.val.factorial : ℂ)*(i.val.choose j.val : ℂ)

theorem factorialHankel_gram_factorization (n : ℕ) :
    factorialHankel n=factorialPascalFactor n*(factorialPascalFactor n).transpose := by
  classical
  ext i j
  rw [Matrix.mul_apply]
  change ((i.val+j.val).factorial : ℂ)=
    ∑ k : Fin n,(i.val.factorial : ℂ)*(i.val.choose k.val : ℂ)*
      ((j.val.factorial : ℂ)*(j.val.choose k.val : ℂ))
  have hs : (∑ k : Fin n,(i.val.choose k.val : ℂ)*(j.val.choose k.val : ℂ))=
      ((i.val+j.val).choose j.val : ℂ) := by
    exact_mod_cast binomial_overlap_sum_fin n i j
  calc
    _=((i.val+j.val).choose j.val : ℂ)*(i.val.factorial : ℂ)*(j.val.factorial : ℂ) := by
      exact_mod_cast (Nat.add_choose_mul_factorial_mul_factorial i.val j.val).symm
    _=(i.val.factorial : ℂ)*(j.val.factorial : ℂ)*
        (∑ k : Fin n,(i.val.choose k.val : ℂ)*(j.val.choose k.val : ℂ)) := by rw [hs];ring
    _=_ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring

theorem factorialHankel_det (n : ℕ) :
    (factorialHankel n).det=∏ i : Fin n,(i.val.factorial : ℂ)^2 := by
  classical
  have htri : (factorialPascalFactor n).IsLowerTriangular := by
    intro i j hij
    change (i.val.factorial : ℂ)*(i.val.choose j.val : ℂ)=0
    rw [Nat.choose_eq_zero_of_lt hij,Nat.cast_zero,mul_zero]
  have hdet : (factorialPascalFactor n).det=∏ i : Fin n,(i.val.factorial : ℂ) := by
    rw [Matrix.det_of_isLowerTriangular _ htri]
    simp [factorialPascalFactor]
  rw [factorialHankel_gram_factorization,Matrix.det_mul,Matrix.det_transpose,hdet]
  rw [← pow_two,Finset.prod_pow]

end
end JinWishart
#print axioms JinWishart.binomial_overlap_sum_fin
#print axioms JinWishart.factorialHankel_gram_factorization
#print axioms JinWishart.factorialHankel_det
