import JinWishartFormalization.MixedCandidateNumerator
import JinWishartFormalization.PositiveDeterminantEnsembleCount

/-! Codex. Seed 2026103002:258 mixed sign/support controls precede source.
The zero extension gives a globally nonnegative formula-side determinant
product. Integrability, normalization and actual law are not asserted.
[需人工审查] Support extension and determinant orientation. -/
open Matrix Finset Function
namespace JinWishart
noncomputable section

def mixedEnsembleF (p L : ℕ) (i : Fin (p+L)) (t : ℝ) : ℝ :=
 if 0 < t then t ^ i.val else 0

def mixedEnsembleG (p L q : ℕ) (lambda : Fin L → ℝ)
 (j : Fin (p+L)) (t : ℝ) : ℝ :=
 if 0 < t then Real.exp (-t)*t^q *
   (match (finSumFinEquiv (m := p) (n := L)).symm j with
    | Sum.inl a => t^a.val
    | Sum.inr b => ∑' m : ℕ, t^m*(noncentralKernelSeriesWeight q m*lambda b^m))
 else 0

theorem mixedDeterminantProduct_eq (p L q : ℕ) (lambda : Fin L → ℝ)
 (x : Fin (p+L) → ℝ) (hx : ∀ i, 0 < x i) :
 determinantProduct (mixedEnsembleF p L) (mixedEnsembleG p L q lambda) x =
 (∏ j : Fin (p+L), Real.exp (-(x j))*x j^q) * mixedSeriesNumerator p L q lambda x := by
 have hA : (Matrix.of (fun i j => mixedEnsembleF p L i (x j))) =
     (Matrix.vandermonde x).transpose := by
   ext i j
   simp [mixedEnsembleF,hx j,Matrix.vandermonde]
 have hB : (Matrix.of (fun i j => mixedEnsembleG p L q lambda i (x j))) =
     Matrix.of (fun i j => (Real.exp (-(x j))*x j^q) *
       (infiniteMixedKernel p L q x lambda).transpose i j) := by
   ext i j
   cases h : (finSumFinEquiv (m := p) (n := L)).symm i <;>
     simp [mixedEnsembleG,hx j,infiniteMixedKernel,Matrix.transpose_apply,h]
 unfold determinantProduct mixedSeriesNumerator
 rw [hA,hB,Matrix.det_transpose,Matrix.det_mul_row,Matrix.det_transpose]
 ring

theorem mixedDeterminantProduct_nonneg (p L q : ℕ) (lambda : Fin L → ℝ)
 (hl : StrictMono lambda) (hlp : ∀ i, 0 < lambda i) (x : Fin (p+L) → ℝ) :
 0 ≤ determinantProduct (mixedEnsembleF p L) (mixedEnsembleG p L q lambda) x := by
 by_cases hx : ∀ i, 0 < x i
 · rw [mixedDeterminantProduct_eq p L q lambda x hx]
   apply mul_nonneg
   · apply Finset.prod_nonneg
     intro j hj
     exact mul_nonneg (Real.exp_pos _).le (pow_nonneg (hx j).le q)
   · exact mixedSeriesNumerator_nonneg p L q lambda x hl hlp hx
 · push_neg at hx
   obtain ⟨j,hj⟩ := hx
   have hz : (Matrix.of (fun i k => mixedEnsembleF p L i (x k))).det = 0 := by
     apply Matrix.det_eq_zero_of_column_eq_zero j
     intro i
     simp [mixedEnsembleF,not_lt.mpr hj]
   unfold determinantProduct
   rw [hz,zero_mul]

end
end JinWishart
#print axioms JinWishart.mixedDeterminantProduct_eq
#print axioms JinWishart.mixedDeterminantProduct_nonneg
