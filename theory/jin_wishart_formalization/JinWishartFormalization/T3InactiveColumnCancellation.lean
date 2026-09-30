import JinWishartFormalization.T3NormalizationAudit
import Mathlib.Tactic.FieldSimp

/-!
# T3 inactive-column normalization: cancellation criterion

This module is an algebraic addendum to `T3NormalizationAudit`. It does not
formalize Appendix C's determinant/integration argument. It records exactly
when the residual inactive-column multivariate factorial can disappear from
the displayed scalar prefactors.
-/

namespace JinWishart.T3NormalizationAudit

noncomputable section

private theorem factorialMultigamma_pos_local (n r : ℕ) :
    0 < factorialMultigamma n r := by
  unfold factorialMultigamma
  apply Finset.prod_pos
  intro i hi
  exact Nat.cast_pos.mpr (Nat.factorial_pos (r - (i.val + 1)))

/-- Under the hypotheses of the scalar audit, equality with the paper's
displayed `c₃` can hold only if either the residual multivariate factorial is
one or `c₃` itself vanishes. This isolates the only purely algebraic escape
from the residual factor; it says nothing about hidden normalizations in the
determinant sum. -/
theorem columnFactors_equal_paperC3_iff_gamma_eq_one_or_c3_zero
    (s t L : ℕ) (hst : s ≤ t) (hLs : L ≤ s)
    (lambda : Fin L → ℝ) (hPos : ∀ i, 0 < lambda i)
    (hDistinct : ∀ i j, i < j → lambda i ≠ lambda j) :
    paperC1 s t L lambda * paperColumnFactorProduct s t L lambda =
        paperC3 s t L lambda ↔
      factorialMultigamma (s - L) (t - L) = 1 ∨
        paperC3 s t L lambda = 0 := by
  have hAudit := paperC1_mul_columnFactors_eq_paperC3_div_inactiveGamma
    s t L hst hLs lambda hPos hDistinct
  have hGammaPos :
      0 < factorialMultigamma (s - L) (t - L) :=
    factorialMultigamma_pos_local (s - L) (t - L)
  rw [hAudit]
  constructor
  · intro hEq
    by_cases hC3 : paperC3 s t L lambda = 0
    · exact Or.inr hC3
    · left
      have hDiv : paperC3 s t L lambda /
          factorialMultigamma (s - L) (t - L) =
          paperC3 s t L lambda := hEq
      have hMul := (div_eq_iff hGammaPos.ne').mp hDiv
      have hCancel : paperC3 s t L lambda * 1 =
          paperC3 s t L lambda * factorialMultigamma (s - L) (t - L) := by
        simpa using hMul
      have hOne := mul_left_cancel₀ hC3 hCancel
      simpa using hOne.symm
  · intro h
    rcases h with hGamma | hC3
    · rw [hGamma]
      simp
    · rw [hC3]
      simp

/-- With positive, pairwise-distinct active eigenvalues, the displayed `c₃`
is nonzero. Thus in this regime the preceding criterion reduces to the
residual multivariate factorial being one. -/
theorem paperC3_ne_zero_of_positive_distinct
    (s t L : ℕ) (lambda : Fin L → ℝ)
    (hPos : ∀ i, 0 < lambda i)
    (hDistinct : ∀ i j, i < j → lambda i ≠ lambda j) :
    paperC3 s t L lambda ≠ 0 := by
  have hGamma : factorialMultigamma (s - L) (s - L) ≠ 0 := by
    unfold factorialMultigamma
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact (Nat.cast_pos.mpr
      (Nat.factorial_pos (s - L - (i.val + 1)))).ne'
  have hV : activeVandermonde lambda ≠ 0 := by
    unfold activeVandermonde
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact sub_ne_zero.mpr (hDistinct i j (Finset.mem_filter.mp hj).2)
  have hPow :
      (∏ i : Fin L, Real.rpow (lambda i) ((2 * (L : ℝ) - s - t) / 2)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact (Real.rpow_pos_of_pos (hPos i) _).ne'
  unfold paperC3
  exact div_ne_zero hPow (mul_ne_zero hGamma hV)

/-- In the concrete dimensions `s=3,t=4,L=1`, the residual factor is two,
so it cannot disappear by factorial cancellation. The separate possibility
`c₃=0` is intentionally left to the hypotheses on active eigenvalues. -/
theorem residualGamma_s3_t4_L1_eq_two :
    factorialMultigamma (3 - 1) (4 - 1) = (2 : ℝ) := by
  rw [factorialMultigamma, Fin.prod_univ_two]
  norm_num

end

end JinWishart.T3NormalizationAudit
