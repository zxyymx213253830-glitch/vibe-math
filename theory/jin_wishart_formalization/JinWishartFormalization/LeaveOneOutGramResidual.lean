import JinWishartFormalization.GaussianSubmatrixLaw
import Mathlib.Algebra.BigOperators.Fin

/-!
# Leave-one-column-out residual geometry

Codex deterministic proofs following actual-sample/QR controls.
No independence between different column residuals is asserted.
[需人工审查] Subsequent connection to actual Gaussian residual laws.
-/
open Matrix
open scoped BigOperators
namespace JinWishart
noncomputable section

def leaveOneOutColumnSpace {m n : ℕ} (A : Matrix (Fin m) (Fin (n+1)) ℂ)
    (j : Fin (n+1)) : Submodule ℂ (EuclideanSpace ℂ (Fin m)) :=
  (A.submatrix id j.succAbove).toEuclideanLin.range

def leaveOneOutResidualEnergy {m n : ℕ} (A : Matrix (Fin m) (Fin (n+1)) ℂ)
    (j : Fin (n+1)) : ℝ :=
  ‖(leaveOneOutColumnSpace A j)ᗮ.starProjection (complexMatrixColumn A j)‖^2

theorem leaveOneOut_other_column_mem {m n : ℕ}
    (A : Matrix (Fin m) (Fin (n+1)) ℂ) (j : Fin (n+1)) (i : Fin n) :
    complexMatrixColumn A (j.succAbove i) ∈ leaveOneOutColumnSpace A j := by
  refine ⟨EuclideanSpace.single i 1,?_⟩
  ext k
  simp [Matrix.toEuclideanLin,Matrix.toLpLin_apply,complexMatrixColumn,
    Matrix.mulVec, dotProduct,EuclideanSpace.single_apply]

theorem matrix_column_sum {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (u : EuclideanSpace ℂ (Fin n)) :
    A.toEuclideanLin u = ∑ j, u j • complexMatrixColumn A j := by
  ext i
  simp [Matrix.toEuclideanLin,Matrix.toLpLin_apply,complexMatrixColumn,
    Matrix.mulVec,dotProduct,Finset.sum_apply,mul_comm]

theorem leaveOneOut_projection_column_sum {m n : ℕ}
    (A : Matrix (Fin m) (Fin (n+1)) ℂ) (j : Fin (n+1))
    (u : EuclideanSpace ℂ (Fin (n+1))) :
    (leaveOneOutColumnSpace A j)ᗮ.starProjection (A.toEuclideanLin u) =
      u j • (leaveOneOutColumnSpace A j)ᗮ.starProjection (complexMatrixColumn A j) := by
  rw [matrix_column_sum,map_sum]
  simp_rw [map_smul]
  rw [Fin.sum_univ_succAbove _ j]
  have hz (i : Fin n) :
      (leaveOneOutColumnSpace A j)ᗮ.starProjection (complexMatrixColumn A (j.succAbove i)) = 0 :=
    Submodule.starProjection_orthogonal_apply_eq_zero (leaveOneOut_other_column_mem A j i)
  simp only [hz,smul_zero,Finset.sum_const_zero,add_zero]

theorem leaveOneOut_coordinate_energy_le {m n : ℕ}
    (A : Matrix (Fin m) (Fin (n+1)) ℂ) (j : Fin (n+1))
    (u : EuclideanSpace ℂ (Fin (n+1))) :
    ‖u j‖^2 * leaveOneOutResidualEnergy A j ≤ ‖A.toEuclideanLin u‖^2 := by
  have h := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    ((leaveOneOutColumnSpace A j)ᗮ.norm_starProjection_apply_le (A.toEuclideanLin u))
  rw [leaveOneOut_projection_column_sum,norm_smul,mul_pow] at h
  exact h

theorem exists_large_unit_coordinate {n : ℕ} (hn : 0 < n)
    (u : EuclideanSpace ℂ (Fin n)) (hu : ‖u‖=1) :
    ∃ j : Fin n, 1 ≤ (n : ℝ)*‖u j‖^2 := by
  classical
  by_contra h
  push_neg at h
  have hs := Finset.sum_lt_sum (s := Finset.univ)
    (fun j _ => (h j).le) ⟨⟨0,hn⟩,Finset.mem_univ _,h _⟩
  rw [← Finset.mul_sum,← EuclideanSpace.norm_sq_eq,hu] at hs
  simp only [one_pow,mul_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one] at hs
  exact (lt_irrefl _ hs)

theorem exists_leaveOneOut_energy_le_dimension_mul {m n : ℕ}
    (A : Matrix (Fin m) (Fin (n+1)) ℂ) (u : EuclideanSpace ℂ (Fin (n+1))) (hu : ‖u‖=1) :
    ∃ j, leaveOneOutResidualEnergy A j ≤ ((n+1 : ℕ) : ℝ)*‖A.toEuclideanLin u‖^2 := by
  obtain ⟨j,hj⟩ := exists_large_unit_coordinate (Nat.succ_pos n) u hu
  refine ⟨j,?_⟩
  have h0 := mul_le_mul_of_nonneg_left (leaveOneOut_coordinate_energy_le A j u)
    (Nat.cast_nonneg (n+1) : (0 : ℝ) ≤ (n+1 : ℕ))
  have h1 := mul_nonneg (sub_nonneg.mpr hj) (sq_nonneg
    ‖(leaveOneOutColumnSpace A j)ᗮ.starProjection (complexMatrixColumn A j)‖)
  change 0 ≤ (((n+1 : ℕ) : ℝ)*‖u j‖^2-1)*leaveOneOutResidualEnergy A j at h1
  nlinarith

end
end JinWishart
#print axioms JinWishart.leaveOneOut_other_column_mem
#print axioms JinWishart.matrix_column_sum
#print axioms JinWishart.leaveOneOut_projection_column_sum
#print axioms JinWishart.leaveOneOut_coordinate_energy_le
#print axioms JinWishart.exists_large_unit_coordinate
#print axioms JinWishart.exists_leaveOneOut_energy_le_dimension_mul
