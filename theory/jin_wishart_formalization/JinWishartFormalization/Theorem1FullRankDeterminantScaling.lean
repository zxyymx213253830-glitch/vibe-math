import JinWishartFormalization.Theorem1Formula

/-!
# Determinant normalization in the full-rank Theorem 1 case

When the noncentrality rank is full, every column of the Theorem 1 matrix is a
Nuttall-Q column. Its row-dependent power-of-two prefactor can therefore be
factored from the determinant and cancels from the normalized determinant
ratio. This isolates the actual Nuttall-Q determinant from the normalization
convention in the paper's entries.
-/

open Matrix

namespace JinWishart

/-- A matrix obtained by multiplying row `i` of `A` by `d i`. -/
def rowScaledMatrix {n : ℕ} (d : Fin n → ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => d i * A i j

/-- The determinant of a row-scaled matrix factors by the product of the
row multipliers. -/
theorem det_rowScaledMatrix {n : ℕ} (d : Fin n → ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    (rowScaledMatrix d A).det = (∏ i, d i) * A.det := by
  simpa [rowScaledMatrix] using Matrix.det_mul_column d A

/-- Common row scaling leaves the ratio of determinant norms unchanged,
provided the unscaled denominator determinant is nonzero. -/
theorem normDetRatio_rowScaledMatrix {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ)
    (hd : ∀ i, d i ≠ 0) (hB : B.det ≠ 0) :
    ‖(rowScaledMatrix d A).det‖ / ‖(rowScaledMatrix d B).det‖ =
      ‖A.det‖ / ‖B.det‖ := by
  have hprod : (∏ i, d i) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (by
      intro i hi
      exact hd i)
  rw [det_rowScaledMatrix, det_rowScaledMatrix, norm_mul, norm_mul]
  have hBnorm : ‖B.det‖ ≠ 0 := norm_ne_zero_iff.mpr hB
  have hscaleNorm : ‖∏ i, d i‖ ≠ 0 := norm_ne_zero_iff.mpr hprod
  field_simp

/-- The row prefactor in Theorem 1. -/
noncomputable def theorem1FullRankRowScale (s t : ℕ) (i : Fin s) : ℂ :=
  (Real.rpow 2
    ((((2 * (i.val + 1) : ℕ) : ℝ) - s - t) / 2) : ℂ)

/-- The full-rank Nuttall-Q matrix before applying the row prefactors in
Theorem 1. -/
noncomputable def theorem1FullRankQMatrix (s t : ℕ) (lambda : Fin s → ℝ) (x : ℝ) :
    Matrix (Fin s) (Fin s) ℂ :=
  fun i j => nuttallQ (theorem1QOrder s t i) (t - s)
    (Real.sqrt (2 * lambda j)) (Real.sqrt (2 * x))

/-- In full rank, the paper's Theorem 1 matrix is exactly the row-scaled
Nuttall-Q matrix. -/
theorem theorem1PsiMatrix_eq_fullRankRowScaledQ
    (s t : ℕ) (hst : s ≤ t) (lambda : Fin s → ℝ) (x : ℝ) :
    theorem1PsiMatrix s t s hst (by omega) lambda x =
      rowScaledMatrix (theorem1FullRankRowScale s t)
        (theorem1FullRankQMatrix s t lambda x) := by
  ext i j
  simp [theorem1PsiMatrix, theorem1PsiEntry, rowScaledMatrix,
    theorem1FullRankRowScale, theorem1FullRankQMatrix]

/-- The row factors are nonzero, so they are legitimate determinant
normalization factors. -/
theorem theorem1FullRankRowScale_ne_zero
    (s t : ℕ) (i : Fin s) : theorem1FullRankRowScale s t i ≠ 0 := by
  simp only [theorem1FullRankRowScale, Complex.ofReal_ne_zero]
  exact (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).ne'

/-- The full-rank Theorem 1 determinant-ratio candidate can be calculated
from the unscaled Nuttall-Q matrix. The assumption records that the paper's
normalizing determinant is nonzero. -/
theorem theorem1FullRankCandidate_eq_unscaledQ
    (s t : ℕ) (hst : s ≤ t) (lambda : Fin s → ℝ) (x : ℝ)
    (hden : (theorem1FullRankQMatrix s t lambda 0).det ≠ 0) :
    theorem1CdfCandidate s t s hst (by omega) lambda x =
      1 - ‖(theorem1FullRankQMatrix s t lambda x).det‖ /
        ‖(theorem1FullRankQMatrix s t lambda 0).det‖ := by
  simp only [theorem1CdfCandidate,
    theorem1PsiMatrix_eq_fullRankRowScaledQ s t hst lambda x,
    theorem1PsiMatrix_eq_fullRankRowScaledQ s t hst lambda 0]
  congr 1
  exact normDetRatio_rowScaledMatrix
    (theorem1FullRankQMatrix s t lambda x)
    (theorem1FullRankQMatrix s t lambda 0)
    (theorem1FullRankRowScale s t)
    (theorem1FullRankRowScale_ne_zero s t) hden

end JinWishart
