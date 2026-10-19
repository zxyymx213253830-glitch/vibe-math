import JinWishartFormalization.WishartProbability
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! Wide/tall full log-det identity by transpose and Sylvester, not spectral padding.
Codex deterministic matrix algebra. -/
open Matrix
namespace JinWishart
noncomputable section

theorem transpose_complexGram_transpose {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℂ) :
    (complexGram Xᵀ)ᵀ = X*Xᴴ := by
  simp only [complexGram,Matrix.transpose_mul,Matrix.transpose_transpose]
  rfl

theorem det_one_add_gram_transpose {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℂ) (r : ℝ) :
    (1+(r : ℂ) • complexGram X).det = (1+(r : ℂ) • complexGram Xᵀ).det := by
  have hsmall : (1+(r : ℂ) • complexGram Xᵀ).det = (1+(r : ℂ) • (X*Xᴴ)).det := by
    rw [← Matrix.det_transpose (1+(r : ℂ) • complexGram Xᵀ)]
    simp only [Matrix.transpose_add,Matrix.transpose_one,Matrix.transpose_smul,
      transpose_complexGram_transpose]
  rw [hsmall]
  simpa only [Matrix.mul_smul,Matrix.smul_mul,complexGram] using
    Matrix.det_one_add_mul_comm Xᴴ ((r : ℂ) • X)

theorem det_rowGram_eq_transposeGram {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℂ) :
    (X*Xᴴ).det=(complexGram Xᵀ).det := by
  rw [← transpose_complexGram_transpose,Matrix.det_transpose]

end
end JinWishart
#print axioms JinWishart.transpose_complexGram_transpose
#print axioms JinWishart.det_one_add_gram_transpose
#print axioms JinWishart.det_rowGram_eq_transposeGram
