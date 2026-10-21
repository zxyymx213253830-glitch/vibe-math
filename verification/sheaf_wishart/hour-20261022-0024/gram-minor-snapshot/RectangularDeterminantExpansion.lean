import JinWishartFormalization.MatrixRankCompression
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! All-function rectangular determinant expansion and coordinate minor witnesses.
Codex finite algebra. This is not yet the subset-grouped Cauchy--Binet formula. -/
open Matrix Finset Function
namespace JinWishart
noncomputable section

theorem det_mul_rectangular_sum_functions {q m : ℕ}
    (A : Matrix (Fin q) (Fin m) ℂ) (B : Matrix (Fin m) (Fin q) ℂ) :
    (A*B).det = ∑ f : Fin q → Fin m, (∏ i, A i (f i))*(B.submatrix f id).det := by
  classical
  have he : A*B = fun i => ∑ j, A i j • B j := by
    ext i k
    simp [Matrix.mul_apply,Finset.sum_apply]
  rw [he]
  change detRowAlternating.toMultilinearMap (fun i => ∑ j, A i j • B j) = _
  rw [MultilinearMap.map_sum]
  apply Finset.sum_congr rfl
  intro f hf
  exact detRowAlternating.map_smul_univ (fun i => A i (f i)) (fun i => B (f i))

theorem det_submatrix_eq_zero_of_not_injective {q m : ℕ}
    (B : Matrix (Fin m) (Fin q) ℂ) (f : Fin q → Fin m) (hf : ¬Injective f) :
    (B.submatrix f id).det=0 := by
  classical
  simp only [Injective] at hf
  push_neg at hf
  obtain ⟨i,j,hij,hne⟩ := hf
  apply Matrix.det_zero_of_row_eq hne
  funext k
  exact congrArg (fun t => B t k) hij

theorem exists_injective_row_minor_of_mul_det_ne_zero {q m : ℕ}
    (A : Matrix (Fin q) (Fin m) ℂ) (B : Matrix (Fin m) (Fin q) ℂ)
    (h : (A*B).det≠0) :
    ∃ f : Fin q → Fin m, Injective f ∧ (B.submatrix f id).det≠0 := by
  classical
  rw [det_mul_rectangular_sum_functions] at h
  obtain ⟨f,hf,hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hd : (B.submatrix f id).det≠0 := (mul_ne_zero_iff.mp hne).2
  refine ⟨f,?_,hd⟩
  by_contra hn
  exact hd (det_submatrix_eq_zero_of_not_injective B f hn)

theorem exists_coordinate_minor_of_compression_det_ne_zero {m n q : ℕ}
    (X : Matrix (Fin m) (Fin n) ℂ) (L : Matrix (Fin q) (Fin m) ℂ)
    (H : Matrix (Fin n) (Fin q) ℂ) (h : (L*X*H).det≠0) :
    ∃ (f : Fin q → Fin m) (g : Fin q → Fin n),
      Injective f ∧ Injective g ∧ (X.submatrix f g).det≠0 := by
  classical
  rw [Matrix.mul_assoc] at h
  obtain ⟨f,hf,hd⟩ := exists_injective_row_minor_of_mul_det_ne_zero L (X*H) h
  have he : (X*H).submatrix f id = X.submatrix f id * H := by
    ext i j
    simp [Matrix.mul_apply]
  rw [he] at hd
  have ht : (H.transpose * (X.submatrix f id).transpose).det≠0 := by
    simpa only [← Matrix.transpose_mul,Matrix.det_transpose] using hd
  obtain ⟨g,hg,hdg⟩ := exists_injective_row_minor_of_mul_det_ne_zero H.transpose
    (X.submatrix f id).transpose ht
  refine ⟨f,g,hf,hg,?_⟩
  have he' : ((X.submatrix f id).transpose.submatrix g id) = (X.submatrix f g).transpose := by
    ext i j
    rfl
  simpa only [he',Matrix.det_transpose] using hdg

theorem exists_rank_coordinate_minor {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℂ) :
    ∃ (f : Fin X.rank → Fin m) (g : Fin X.rank → Fin n),
      Injective f ∧ Injective g ∧ (X.submatrix f g).det≠0 := by
  obtain ⟨L,H,hLH⟩ := matrix_rank_compression X
  apply exists_coordinate_minor_of_compression_det_ne_zero X L H
  rw [hLH,Matrix.det_one]
  exact one_ne_zero

end
end JinWishart
#print axioms JinWishart.det_mul_rectangular_sum_functions
#print axioms JinWishart.det_submatrix_eq_zero_of_not_injective
#print axioms JinWishart.exists_injective_row_minor_of_mul_det_ne_zero
#print axioms JinWishart.exists_coordinate_minor_of_compression_det_ne_zero
#print axioms JinWishart.exists_rank_coordinate_minor
