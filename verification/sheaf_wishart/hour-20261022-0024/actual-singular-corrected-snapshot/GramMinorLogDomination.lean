import JinWishartFormalization.GramMinorCoefficientBound
import JinWishartFormalization.PositiveSpectrumLogIntegrability

/-! Fixed-coordinate-minor domination of the total positive-spectrum logarithm.
Codex deterministic algebra/calculus; a nonzero minor is an explicit premise. -/
open Matrix Polynomial
namespace JinWishart
noncomputable section

theorem gram_rank_coefficient_log_eq_ordered_positive_sum {m n : ℕ}
    (X : Matrix (Fin m) (Fin n) ℂ) :
    Real.log (((1+(Polynomial.X : ℂ[X]) • (complexGram X).map Polynomial.C).det).coeff X.rank).re =
      ∑ i, positiveSpectrumLog ((complexGram_posSemidef X).1.eigenvalues₀ i) := by
  classical
  let h := (complexGram_posSemidef X).1
  let e : Fin (Fintype.card (Fin n)) ≃ Fin n :=
    Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))
  have hs : (∑ i, positiveSpectrumLog (h.eigenvalues₀ i)) =
      ∑ i, positiveSpectrumLog (h.eigenvalues i) := by
    simpa only [Matrix.IsHermitian.eigenvalues,e,Equiv.symm_apply_apply] using
      Equiv.sum_comp e (fun i => positiveSpectrumLog (h.eigenvalues i))
  rw [gram_rank_coefficient_log_eq_positive_sum]
  simpa only [positiveSpectrumLog] using hs.symm

theorem abs_positive_log_sum_le_minor_log {m n q : ℕ}
    (X : Matrix (Fin m) (Fin n) ℂ) (f : Fin q → Fin m) (g : Fin q → Fin n)
    (hg : Function.Injective g) (hr : X.rank=q) (hp : (X.submatrix f g).det≠0) :
    |∑ i, positiveSpectrumLog ((complexGram_posSemidef X).1.eigenvalues₀ i)| ≤
      (∑ i, (complexGram_posSemidef X).1.eigenvalues₀ i)+|Real.log (q.factorial : ℝ)|+
        2*|Real.log ‖(X.submatrix f g).det‖| := by
  classical
  have hb := squared_coordinate_minor_le_factorial_coefficient X f g hg
  have hc : 0 < (((1+(Polynomial.X : ℂ[X]) • (complexGram X).map Polynomial.C).det).coeff q).re := by
    rw [← hr]
    exact gram_rank_coefficient_re_pos X
  have hf : 0 < (q.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos q)
  have hn : 0 < Complex.normSq ((X.submatrix f g).det) := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_pos (norm_pos_iff.mpr hp) 2
  have hl := (Real.log_le_log_iff hn (mul_pos hf hc)).2 hb
  rw [Complex.normSq_eq_norm_sq,Real.log_pow,Real.log_mul hf.ne' hc.ne'] at hl
  have he : Real.log (((1+(Polynomial.X : ℂ[X]) • (complexGram X).map Polynomial.C).det).coeff q).re =
      ∑ i, positiveSpectrumLog ((complexGram_posSemidef X).1.eigenvalues₀ i) := by
    rw [← hr]
    exact gram_rank_coefficient_log_eq_ordered_positive_sum X
  rw [he] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hu : (∑ i, positiveSpectrumLog ((complexGram_posSemidef X).1.eigenvalues₀ i)) ≤
      ∑ i, (complexGram_posSemidef X).1.eigenvalues₀ i :=
    Finset.sum_le_sum (fun i _ => positiveSpectrumLog_le_self (complexGram_eigenvalues₀_nonneg X i))
  have ht : 0 ≤ ∑ i, (complexGram_posSemidef X).1.eigenvalues₀ i :=
    Finset.sum_nonneg (fun i _ => complexGram_eigenvalues₀_nonneg X i)
  apply abs_le.mpr
  constructor
  · linarith [neg_le_abs (Real.log ‖(X.submatrix f g).det‖),le_abs_self (Real.log (q.factorial : ℝ))]
  · linarith [abs_nonneg (Real.log (q.factorial : ℝ)),abs_nonneg (Real.log ‖(X.submatrix f g).det‖)]

end
end JinWishart
#print axioms JinWishart.gram_rank_coefficient_log_eq_ordered_positive_sum
#print axioms JinWishart.abs_positive_log_sum_le_minor_log
