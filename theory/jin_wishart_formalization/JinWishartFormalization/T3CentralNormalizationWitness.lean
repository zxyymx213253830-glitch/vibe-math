import JinWishartFormalization.T3ScalarNormalizationBridge
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Exact central T3 normalization witness

This tests two explicit SOURCE-TRANSCRIBED mixed-row determinants, not an
assumed spectral density or an asserted equality with the generic sum API.
The instance is s=2,t=3,L=0,k=2,x=2. The result cannot be a probability.
It concerns the current arXiv v2 transcription only; the final journal version,
errata and interpretation of Theta still require independent review.
-/

open Matrix Finset
namespace JinWishart
noncomputable section

def emptyNoncentralSpectrum : OrderedPositiveNoncentralSpectrum 0 where
  values := Fin.elim0
  positive := fun i => Fin.elim0 i
  strictAnti := fun i => Fin.elim0 i

private theorem upperGamma_at_two (k : ℕ) (hk : k ≤ 3) :
    upperGammaNat k 2 =
      (if k = 0 then 1 else if k = 1 then 3 else if k = 2 then 10 else 38) *
        (Real.exp (-2) : ℂ) := by
  interval_cases k <;>
    norm_num [upperGammaNat_eq_finite _ (by norm_num : (0 : ℝ) ≤ 2),
      upperGammaNatFinite, Finset.sum_range_succ, ← Complex.ofReal_exp] <;> ring

private theorem psi_entry (i j : Fin 2) :
    theorem1PsiMatrix 2 3 0 (by decide) (by decide)
        emptyNoncentralSpectrum.values 2 i j =
      (!![38, 10; 10, 3] : Matrix (Fin 2) (Fin 2) ℂ) i j *
        (Real.exp (-2) : ℂ) := by
  fin_cases i <;> fin_cases j <;>
    norm_num [theorem1PsiMatrix, theorem1PsiEntry, theorem1GammaIndex,
      upperGamma_at_two]

private theorem psi_zero_entry (i j : Fin 2) :
    theorem1PsiMatrix 2 3 0 (by decide) (by decide)
        emptyNoncentralSpectrum.values 0 i j =
      (!![6, 2; 2, 1] : Matrix (Fin 2) (Fin 2) ℂ) i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [theorem1PsiMatrix, theorem1PsiEntry, theorem1GammaIndex,
      upperGammaNat_at_zero_eq_factorial]

private theorem xi_entry (i j : Fin 2) :
    theorem2XiMatrix 2 3 0 (by decide) (by decide)
        emptyNoncentralSpectrum.values 2 i j =
      (!![6, 2; 2, 1] : Matrix (Fin 2) (Fin 2) ℂ) i j -
        (!![38, 10; 10, 3] : Matrix (Fin 2) (Fin 2) ℂ) i j *
          (Real.exp (-2) : ℂ) := by
  have h := congrFun (congrFun
    (theorem2XiMatrix_add_theorem1PsiMatrix 2 3 0 (by decide) (by decide)
      emptyNoncentralSpectrum.values 2) i) j
  simp only [Matrix.add_apply, psi_entry, psi_zero_entry] at h
  exact eq_sub_of_add_eq h

/-- The two explicit allowed row selections in the central s=2,k=2 case.
The bridge to the generic powerset-sum API is deliberately not asserted. -/
def centralTwoThreeMixedRowSum : ℂ :=
  (theorem3ThetaMatrix 2 3 0 (by decide) (by decide)
    emptyNoncentralSpectrum 2 {0}).det +
  (theorem3ThetaMatrix 2 3 0 (by decide) (by decide)
    emptyNoncentralSpectrum 2 {1}).det

/-- Exact evaluation of the explicit two mixed-row determinants. -/
theorem theorem3CentralTwoThree_at_two :
    centralTwoThreeMixedRowSum =
        (16 * Real.exp (-2) - 28 * (Real.exp (-2)) ^ 2 : ℝ) := by
  simp [centralTwoThreeMixedRowSum, theorem3ThetaMatrix,
    rowMix, Matrix.det_fin_two, psi_entry, xi_entry]
  ring

/-- A rigorous bound, using mathlib's proved exponential bounds, not numerical sampling. -/
theorem theorem3CentralTwoThree_at_two_gt_one :
    1 < centralTwoThreeMixedRowSum.re := by
  rw [theorem3CentralTwoThree_at_two]
  simp only [Complex.ofReal_re]
  have hlo := Real.exp_one_gt_two
  have hhi := Real.exp_one_lt_three
  have hp := Real.exp_pos (1 : ℝ)
  have he : Real.exp (-2) = 1 / (Real.exp 1) ^ 2 := by
    rw [Real.exp_neg]
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    simp [pow_two, one_div]
  rw [he]
  have hylo : 4 < (Real.exp 1) ^ 2 := by nlinarith
  have hyhi : (Real.exp 1) ^ 2 < 9 := by nlinarith
  have hyp : 0 < (Real.exp 1) ^ 2 := sq_pos_of_pos hp
  have hpoly : (Real.exp 1) ^ 2 * (Real.exp 1) ^ 2 <
      16 * (Real.exp 1) ^ 2 - 28 := by
    nlinarith [sq_nonneg ((Real.exp 1) ^ 2 - 4),
      mul_pos (sub_pos.mpr hylo) (sub_pos.mpr hyhi)]
  apply (mul_lt_mul_iff_of_pos_right (mul_pos hyp hyp)).mp
  field_simp
  nlinarith

end
end JinWishart
