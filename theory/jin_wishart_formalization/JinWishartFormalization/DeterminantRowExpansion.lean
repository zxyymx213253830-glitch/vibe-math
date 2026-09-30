import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

open Finset

namespace JinWishart

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [CommRing R]

/-- The matrix whose rows in `S` come from `A` and all other rows from `B`. -/
def rowMix (A B : Matrix n n R) (S : Finset n) : Matrix n n R :=
  fun i j => if i ∈ S then A i j else B i j

theorem det_updateRow_add_of_rows (M A B : Matrix n n R) (i : n) :
      (M.updateRow i (A i + B i)).det =
        (M.updateRow i (A i)).det + (M.updateRow i (B i)).det := by
  exact Matrix.det_updateRow_add M i (A i) (B i)

theorem prod_add_eq_sum_powerset (f g : n → R) :
    (∏ i, (f i + g i)) =
      ∑ S ∈ Finset.univ.powerset,
        (∏ i ∈ S, f i) * ∏ i ∈ Finset.univ \ S, g i := by
  classical
  simpa using (Finset.prod_add f g (Finset.univ : Finset n))

theorem prod_rowMix (A B : Matrix n n R) (S : Finset n) (σ : Equiv.Perm n) :
    (∏ i, rowMix A B S i (σ i)) =
      (∏ i ∈ S, A i (σ i)) * ∏ i ∈ Finset.univ \ S, B i (σ i) := by
  classical
  calc
    (∏ i, rowMix A B S i (σ i)) =
        ∏ i, ((if i ∈ S then A i (σ i) else 1) *
          (if i ∈ S then 1 else B i (σ i))) := by
      apply Finset.prod_congr rfl
      intro i hi
      by_cases h : i ∈ S <;> simp [rowMix, h]
    _ = (∏ i, if i ∈ S then A i (σ i) else 1) *
          ∏ i, if i ∈ S then 1 else B i (σ i) := Finset.prod_mul_distrib
    _ = (∏ i ∈ S, A i (σ i)) * ∏ i ∈ Finset.univ \ S, B i (σ i) := by
      congr 1
      · rw [Finset.prod_ite_mem_eq]
      · rw [← Finset.prod_ite_mem_eq (s := Finset.univ \ S)
          (f := fun i => B i (σ i))]
        apply Finset.prod_congr rfl
        intro i hi
        by_cases h : i ∈ S <;> simp [h]

theorem det_apply_rows (M : Matrix n n R) :
    M.det = ∑ σ : Equiv.Perm n,
      ((Equiv.Perm.sign σ : ℤ) : R) * ∏ i, M i (σ i) := by
  rw [← Matrix.det_transpose, Matrix.det_apply']
  simp only [Matrix.transpose_apply]

theorem det_add_eq_sum_rowMix (A B : Matrix n n R) :
    (A + B).det = ∑ S ∈ Finset.univ.powerset, (rowMix A B S).det := by
  classical
  simp_rw [det_apply_rows]
  simp only [Matrix.add_apply]
  calc
    (∑ σ : Equiv.Perm n,
        ((Equiv.Perm.sign σ : ℤ) : R) *
          ∏ i, (A i (σ i) + B i (σ i))) =
      ∑ σ : Equiv.Perm n,
        ((Equiv.Perm.sign σ : ℤ) : R) *
          ∑ S ∈ Finset.univ.powerset,
            (∏ i ∈ S, A i (σ i)) * ∏ i ∈ Finset.univ \ S, B i (σ i) := by
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [prod_add_eq_sum_powerset]
    _ = ∑ σ : Equiv.Perm n, ∑ S ∈ Finset.univ.powerset,
          ((Equiv.Perm.sign σ : ℤ) : R) *
            ((∏ i ∈ S, A i (σ i)) * ∏ i ∈ Finset.univ \ S, B i (σ i)) := by
      simp_rw [Finset.mul_sum]
    _ = ∑ S ∈ Finset.univ.powerset, ∑ σ : Equiv.Perm n,
          ((Equiv.Perm.sign σ : ℤ) : R) *
            ((∏ i ∈ S, A i (σ i)) * ∏ i ∈ Finset.univ \ S, B i (σ i)) := by
      rw [Finset.sum_comm]
    _ = ∑ S ∈ Finset.univ.powerset, ∑ σ : Equiv.Perm n,
          ((Equiv.Perm.sign σ : ℤ) : R) *
            ∏ i, rowMix A B S i (σ i) := by
      apply Finset.sum_congr rfl
      intro S hS
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [prod_rowMix]

end JinWishart
