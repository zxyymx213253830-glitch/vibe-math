import JinWishartFormalization.GramMinimumRayleigh
import JinWishartFormalization.GramMinimumResidualUpper
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Least Gram eigenvalue under an invertible column transformation

Rank-free deterministic bounds. A may be singular; only B is invertible.
Codex. [需人工审查] Later covariance interpretation, not a new density assumption.
-/
open Matrix
namespace JinWishart
noncomputable section

def matrixColumnControl {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  max 1 (‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) B‖^2)

theorem matrixColumnControl_pos {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) :
    0<matrixColumnControl B := by
  unfold matrixColumnControl
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ)<1) (le_max_left (1 : ℝ) _)

theorem matrixColumn_energy_bound {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (u : EuclideanSpace ℂ (Fin n)) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) B u‖^2 ≤ matrixColumnControl B*‖u‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) B u))
    ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) B).le_opNorm u) 2
  rw [mul_pow] at h
  exact h.trans (mul_le_mul_of_nonneg_right (show ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) B‖^2 ≤ matrixColumnControl B from (by unfold matrixColumnControl; exact le_max_right (1 : ℝ) _)) (sq_nonneg _))

theorem matrixColumn_composition {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (B : Matrix (Fin n) (Fin n) ℂ) (u : EuclideanSpace ℂ (Fin n)) :
    (A*B).toEuclideanLin u = A.toEuclideanLin (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) B u) := by
  ext i
  change ((A*B)*ᵥ (⇑u)) i = (A*ᵥ (B*ᵥ (⇑u))) i
  rw [Matrix.mulVec_mulVec]

theorem gramSmallestValue_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (hn : 0<n) :
    0≤gramSmallestValue A hn := by
  obtain ⟨u,_,he⟩ := exists_gram_minimum_unit_vector A hn
  rw [← he]
  exact sq_nonneg _

theorem matrixColumn_inverse_apply {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (hB : IsUnit B.det) (u : EuclideanSpace ℂ (Fin n)) :
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) B (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) B⁻¹ u) = u := by
  have h := congrArg (fun T : Matrix (Fin n) (Fin n) ℂ => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) T u)
    (B.mul_nonsing_inv hB)
  simpa only [map_mul,map_one,mul_apply_eq_comp,one_apply_eq_self] using h

theorem gramSmallestValue_mul_column_upper {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (B : Matrix (Fin n) (Fin n) ℂ) (hn : 0<n) (hB : IsUnit B.det) :
    gramSmallestValue (A*B) hn ≤ matrixColumnControl B*gramSmallestValue A hn := by
  obtain ⟨w,hw,he⟩ := exists_gram_minimum_unit_vector A hn
  let u := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) B⁻¹ w
  have hBu : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) B u=w := matrixColumn_inverse_apply B hB w
  have hbound := matrixColumn_energy_bound B u
  rw [hBu,hw,one_pow] at hbound
  have hRay := gramSmallestValue_rayleigh_lower (A*B) hn u
  rw [matrixColumn_composition,hBu,he] at hRay
  calc
    gramSmallestValue (A*B) hn = gramSmallestValue (A*B) hn*1 := by ring
    _ ≤ gramSmallestValue (A*B) hn*(matrixColumnControl B*‖u‖^2) :=
      mul_le_mul_of_nonneg_left hbound (gramSmallestValue_nonneg _ hn)
    _ = matrixColumnControl B*(gramSmallestValue (A*B) hn*‖u‖^2) := by ring
    _ ≤ matrixColumnControl B*gramSmallestValue A hn :=
      mul_le_mul_of_nonneg_left hRay (matrixColumnControl_pos B).le

theorem gramSmallestValue_mul_column_lower {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (B : Matrix (Fin n) (Fin n) ℂ) (hn : 0<n) (hB : IsUnit B.det) :
    gramSmallestValue A hn ≤ matrixColumnControl B⁻¹*gramSmallestValue (A*B) hn := by
  have hBinv : IsUnit (B⁻¹).det := Matrix.isUnit_det_of_left_inverse (B.mul_nonsing_inv hB)
  have h := gramSmallestValue_mul_column_upper (A*B) B⁻¹ hn hBinv
  rw [Matrix.mul_assoc,B.mul_nonsing_inv hB,Matrix.mul_one] at h
  exact h

end
end JinWishart
#print axioms JinWishart.matrixColumnControl_pos
#print axioms JinWishart.matrixColumn_energy_bound
#print axioms JinWishart.matrixColumn_composition
#print axioms JinWishart.gramSmallestValue_nonneg
#print axioms JinWishart.matrixColumn_inverse_apply
#print axioms JinWishart.gramSmallestValue_mul_column_upper
#print axioms JinWishart.gramSmallestValue_mul_column_lower
