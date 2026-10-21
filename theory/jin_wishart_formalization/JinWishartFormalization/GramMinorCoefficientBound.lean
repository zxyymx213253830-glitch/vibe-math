import JinWishartFormalization.AveragedCauchyBinet
import JinWishartFormalization.GramRankSpectralCoefficient
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! A single injective column selection is bounded by the Gram coefficient.
The row-selection bound retains the harmless factorial from averaging.
Codex deterministic finite algebra; no stochastic integrability claimed. -/
open Matrix Polynomial Finset Function
open scoped ComplexOrder
namespace JinWishart
noncomputable section

theorem selected_gram_det_le_coefficient {m n q : ℕ}
    (X : Matrix (Fin m) (Fin n) ℂ) (g : Fin q → Fin n) (hg : Injective g) :
    (complexGram (X.submatrix id g)).det.re ≤
      (((1+(Polynomial.X : ℂ[X]) • (complexGram X).map Polynomial.C).det).coeff q).re := by
  classical
  let S := Finset.univ.image g
  let f : Fin q → S := fun i => ⟨g i,Finset.mem_image_of_mem g (Finset.mem_univ i)⟩
  have hf : Bijective f := by
    constructor
    · intro i j hij
      exact hg (congrArg Subtype.val hij)
    · intro j
      obtain ⟨i,hi,hij⟩ := Finset.mem_image.mp j.property
      exact ⟨i,Subtype.ext hij⟩
  let e : Fin q ≃ S := Equiv.ofBijective f hf
  have he : ((complexGram X).submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n)).submatrix e e =
      complexGram (X.submatrix id g) := by
    ext i j
    rfl
  have hd : ((complexGram X).submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n)).det =
      (complexGram (X.submatrix id g)).det := by
    rw [← he,Matrix.det_submatrix_equiv_self]
  have hS : S ∈ Finset.univ.powersetCard q := by
    simp [S,Finset.mem_powersetCard,Finset.card_image_of_injective _ hg]
  have hcoeff : (((1+(Polynomial.X : ℂ[X]) • (complexGram X).map Polynomial.C).det).coeff q).re =
      ∑ s ∈ Finset.univ.powersetCard q,
        ((complexGram X).submatrix (Subtype.val : s → Fin n) (Subtype.val : s → Fin n)).det.re := by
    simpa using congrArg Complex.re (Matrix.coeff_det_one_add_X_smul_eq_sum_minors (complexGram X) q)
  rw [hcoeff,← hd]
  refine Finset.single_le_sum (s := Finset.univ.powersetCard q)
    (f := fun s : Finset (Fin n) =>
      ((complexGram X).submatrix (Subtype.val : s → Fin n) (Subtype.val : s → Fin n)).det.re) ?_ hS
  intro s hs
  exact (RCLike.nonneg_iff.mp
    (((complexGram_posSemidef X).submatrix (Subtype.val : s → Fin n)).det_nonneg)).1

theorem squared_coordinate_minor_le_factorial_coefficient {m n q : ℕ}
    (X : Matrix (Fin m) (Fin n) ℂ) (f : Fin q → Fin m) (g : Fin q → Fin n)
    (hg : Injective g) :
    Complex.normSq ((X.submatrix f g).det) ≤ (q.factorial : ℝ)*
      (((1+(Polynomial.X : ℂ[X]) • (complexGram X).map Polynomial.C).det).coeff q).re := by
  have h := squared_minor_le_factorial_gram_det (X.submatrix id g) f
  have he : (X.submatrix id g).submatrix f id = X.submatrix f g := rfl
  rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_left (selected_gram_det_le_coefficient X g hg) (Nat.cast_nonneg _))

end
end JinWishart
#print axioms JinWishart.selected_gram_det_le_coefficient
#print axioms JinWishart.squared_coordinate_minor_le_factorial_coefficient
