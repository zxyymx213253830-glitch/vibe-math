import JinWishartFormalization.CentralWishartCone
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# A dimension-independent block step for the central matrix-density route

Pure factorization, determinant and cone geometry. This is NOT the missing
Gaussian-to-matrix density: conditional laws, real Hermitian volume and the
Jacobian remain separate obligations. [需人工审查] Their eventual model use.
-/

open Matrix
open scoped ComplexOrder
namespace JinWishart
noncomputable section

def centralBlockShear {m n : ℕ} (U : Matrix (Fin n) (Fin m) ℂ) :
    Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ :=
  Matrix.fromBlocks 1 0 U 1

def centralBlockStep {m n : ℕ} (A : Matrix (Fin m) (Fin m) ℂ)
    (U : Matrix (Fin n) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ :=
  Matrix.fromBlocks A (A * Uᴴ) (U * A) (B + U * A * Uᴴ)

theorem centralBlockShear_det {m n : ℕ} (U : Matrix (Fin n) (Fin m) ℂ) :
    (centralBlockShear U).det = 1 := by
  simp [centralBlockShear, Matrix.det_fromBlocks_zero₁₂]

theorem centralBlockShear_isUnit {m n : ℕ} (U : Matrix (Fin n) (Fin m) ℂ) :
    IsUnit (centralBlockShear U) := by
  rw [Matrix.isUnit_iff_isUnit_det, centralBlockShear_det]
  exact isUnit_one

/-- Block congruence factors the extension in every pair of dimensions. -/
theorem centralBlockStep_factor {m n : ℕ} (A : Matrix (Fin m) (Fin m) ℂ)
    (U : Matrix (Fin n) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) :
    centralBlockStep A U B = centralBlockShear U *
      Matrix.fromBlocks A 0 0 B * (centralBlockShear U)ᴴ := by
  have hs : (centralBlockShear U)ᴴ = Matrix.fromBlocks 1 Uᴴ 0 1 := by
    ext i j
    cases i <;> cases j <;> simp [centralBlockShear, Matrix.conjTranspose_apply, Matrix.one_apply, eq_comm]
  rw [hs]
  simp [centralBlockStep, centralBlockShear, Matrix.fromBlocks_multiply,
    Matrix.mul_assoc, add_comm]

theorem centralBlockStep_det {m n : ℕ} (A : Matrix (Fin m) (Fin m) ℂ)
    (U : Matrix (Fin n) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) :
    (centralBlockStep A U B).det = A.det * B.det := by
  rw [centralBlockStep_factor, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_conjTranspose, centralBlockShear_det]
  simp [Matrix.det_fromBlocks_zero₂₁]

/-- Exact cone equivalence; no density or probability identity is assumed. -/
theorem centralBlockStep_posDef_iff {m n : ℕ} (A : Matrix (Fin m) (Fin m) ℂ)
    (U : Matrix (Fin n) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) :
    (centralBlockStep A U B).PosDef ↔ (Matrix.fromBlocks A 0 0 B).PosDef := by
  rw [centralBlockStep_factor]
  exact (centralBlockShear_isUnit U).posDef_star_right_conjugate_iff

end
end JinWishart

#print axioms JinWishart.centralBlockShear_det
#print axioms JinWishart.centralBlockShear_isUnit
#print axioms JinWishart.centralBlockStep_factor
#print axioms JinWishart.centralBlockStep_det
#print axioms JinWishart.centralBlockStep_posDef_iff
