import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import JinWishartFormalization.CentralWishartDensityAlgebra

/-! Finite principal-minor expansion of a scalar matrix shift.
Codex proof bodies; reuses the locked multilinear determinant API.
-/
open Matrix
open MeasureTheory
open scoped ENNReal ComplexOrder
namespace JinWishart
noncomputable section

theorem det_add_scalar_eq_sum_principalMinors {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (x : ℂ) :
    (A + x • 1).det = ∑ S : Finset (Fin n), x ^ (n - S.card) *
      (A.submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n)).det := by
  classical
  let D := (Matrix.detRowAlternating : (Fin n → ℂ) [⋀^Fin n]→ₗ[ℂ] ℂ)
  change D ((fun i => A i) + (fun i => (x • (1 : Matrix (Fin n) (Fin n) ℂ)) i)) = _
  rw [D.map_add_univ]
  apply Finset.sum_congr rfl
  intro S _
  have he : S.piecewise (fun i => A i) (fun i => (x • (1 : Matrix (Fin n) (Fin n) ℂ)) i) =
      fun i => (if i ∈ S then (1 : ℂ) else x) •
        S.piecewise (fun i => A i) (fun i => (1 : Matrix (Fin n) (Fin n) ℂ) i) i := by
    funext i j
    simp only [Finset.piecewise, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp [Matrix.smul_apply, smul_eq_mul]
  rw [he, D.map_smul_univ]
  have hp : (∏ i : Fin n, if i ∈ S then (1 : ℂ) else x) = x ^ (n - S.card) := by
    rw [Finset.prod_ite]
    simp only [Finset.prod_const_one, one_mul, Finset.prod_const]
    congr 1
    have heq : Finset.univ.filter (fun i : Fin n => i ∉ S) = Finset.univ \ S := by
      ext i
      simp
    rw [heq]
    simp [Finset.card_sdiff]
  rw [hp]
  change _ * (Matrix.of (S.piecewise A (1 : Matrix (Fin n) (Fin n) ℂ))).det = _
  exact congrArg (fun z : ℂ => x ^ (n - S.card) * z)
    (Matrix.det_piecewise_one_eq_submatrix_det A S)

theorem ofReal_det_add_scalar_eq_sum_principalMinors {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef) (x : ℝ) (hx : 0 ≤ x) :
    ENNReal.ofReal (A + (x : ℂ) • 1).det.re =
      ∑ S : Finset (Fin n), ENNReal.ofReal (x ^ (n - S.card)) *
        ENNReal.ofReal (A.submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n)).det.re := by
  classical
  rw [det_add_scalar_eq_sum_principalMinors, Complex.re_sum]
  have he (S : Finset (Fin n)) : ((x : ℂ) ^ (n - S.card) *
      (A.submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n)).det).re =
      x ^ (n - S.card) * (A.submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n)).det.re := by
    rw [← Complex.ofReal_pow]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  simp_rw [he]
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro S _
    exact ENNReal.ofReal_mul (pow_nonneg hx _)
  · intro S _
    exact mul_nonneg (pow_nonneg hx _) (Complex.nonneg_iff.mp (hA.submatrix _).det_nonneg).1

end
end JinWishart

#print axioms JinWishart.det_add_scalar_eq_sum_principalMinors
#print axioms JinWishart.ofReal_det_add_scalar_eq_sum_principalMinors
