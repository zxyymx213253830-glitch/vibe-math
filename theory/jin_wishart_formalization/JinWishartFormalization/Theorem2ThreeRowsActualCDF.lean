import JinWishartFormalization.Theorem2SingleColumnAnyRows
import JinWishartFormalization.Theorem1ThreeRowsActualCDF

/-!
# Theorem 2 in the actual three-row, one-column noncentral model

This module is the one-column specialization `(s,t,L)=(1,3,1)`.  Since the
Gram matrix has one eigenvalue, its maximum and minimum coincide.  The proof
reduces the Theorem 2 absolute Nuttall-Q increment to the already formalized
Theorem 1 CDF, using the real nonnegative radial-tail representation.
-/

open MeasureTheory ProbabilityTheory Set

namespace JinWishart

noncomputable section

/-- For every deterministic complex `3 × 1` mean, the paper's Theorem 2
candidate at `(s,t,L)=(1,3,1)` equals the actual CDF of its unique Gram
eigenvalue (thus both the largest and smallest eigenvalue CDFs). The parameter
`lambda` is half the squared norm of the mean in the repository's six-real-
coordinate sample encoding. -/
theorem theorem2ThreeRowsOneColumnCandidate_eq_actualCDF
    (M : Matrix (Fin 3) (Fin 1) ℂ) (lambda x : ℝ)
    (hlambda : 0 < lambda) (hx : 0 ≤ x)
    (hmean : ‖threeRowSampleToFin6 (complexSampleMean M)‖ ^ 2 = 2 * lambda) :
    theorem2CdfCandidate 1 3 1 (by omega) (by omega)
        (fun _ : Fin 1 => lambda) x =
      cdf ((stdGaussian (ComplexSample (m := 3) (n := 1))).map
        (complexNoncentralSampleSmallestEigenvalue
          M (by norm_num))) x := by
  let a : ℝ := Real.sqrt (2 * lambda)
  let b : ℝ := Real.sqrt (2 * x)
  have ha : 0 < a := by
    dsimp [a]
    exact Real.sqrt_pos.2 (by positivity)
  have hb : 0 ≤ b := by dsimp [b]; exact Real.sqrt_nonneg _
  have hqzero : nuttallQ 3 2 a 0 = (a ^ 2 : ℂ) :=
    nuttallQ32_zero_eq_sq a ha.ne'
  have hden : nuttallQ 3 2 a 0 ≠ 0 := by
    rw [hqzero]
    exact_mod_cast (pow_ne_zero 2 ha.ne')
  have hnormzero : ‖nuttallQ 3 2 a 0‖ = a ^ 2 := by
    rw [hqzero, ← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (sq_pos_of_ne_zero ha.ne')]
  have htotal :
      ∫ r in Ioi (0 : ℝ), noncentralChiSixRadialSeriesKernel a r = 1 :=
    noncentralChiSixRadialSeriesKernel_integral_eq_one a
  have hmono :
      ∫ r in Ioi b, noncentralChiSixRadialSeriesKernel a r ≤
        ∫ r in Ioi (0 : ℝ), noncentralChiSixRadialSeriesKernel a r := by
    apply setIntegral_mono_set (integrableOn_noncentralChiSixRadialSeriesKernel a)
      ?_ (Ioi_subset_Ioi hb).eventuallySubset
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact noncentralChiSixRadialSeriesKernel_nonneg a r (le_of_lt hr)
  have htail_nonneg : 0 ≤
      ∫ r in Ioi b, noncentralChiSixRadialSeriesKernel a r :=
    setIntegral_nonneg measurableSet_Ioi fun r hr =>
      noncentralChiSixRadialSeriesKernel_nonneg a r
        (le_of_lt (lt_of_le_of_lt hb hr))
  have htail_le_one :
      ∫ r in Ioi b, noncentralChiSixRadialSeriesKernel a r ≤ 1 := by
    calc
      _ ≤ ∫ r in Ioi (0 : ℝ), noncentralChiSixRadialSeriesKernel a r := hmono
      _ = 1 := htotal
  have hQb : nuttallQ 3 2 a b =
      ((a ^ 2 * ∫ r in Ioi b,
        noncentralChiSixRadialSeriesKernel a r : ℝ) : ℂ) :=
    nuttallQ32_eq_ofReal_scaledRadialTail a b ha.ne' hb
  have hdiff : nuttallQ 3 2 a 0 - nuttallQ 3 2 a b =
      ((a ^ 2 - a ^ 2 * ∫ r in Ioi b,
        noncentralChiSixRadialSeriesKernel a r : ℝ) : ℂ) := by
    rw [hqzero, hQb]
    push_cast
    ring
  have hdiff_nonneg : 0 ≤ a ^ 2 - a ^ 2 *
      ∫ r in Ioi b, noncentralChiSixRadialSeriesKernel a r := by
    have hmul := mul_le_mul_of_nonneg_left htail_le_one (sq_nonneg a)
    nlinarith
  have hnormdiff :
      ‖nuttallQ 3 2 a 0 - nuttallQ 3 2 a b‖ =
        a ^ 2 - a ^ 2 * ∫ r in Ioi b,
          noncentralChiSixRadialSeriesKernel a r := by
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hdiff_nonneg]
  have hratio :
      ‖nuttallQ 3 2 a 0 - nuttallQ 3 2 a b‖ /
          ‖nuttallQ 3 2 a 0‖ =
        1 - ∫ r in Ioi b, noncentralChiSixRadialSeriesKernel a r := by
    rw [hnormdiff, hnormzero]
    have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha.ne'
    field_simp [ha2]
  rw [theorem2OneColumnCandidate_eq_normalizedNuttallQIncrement
    3 (by omega) lambda x hden]
  rw [← theorem1ThreeRowsOneColumnCandidate_eq_actualCDF
    M lambda x hlambda hx hmean]
  rw [theorem1OneColumnCandidate_eq_normalizedNuttallQ
    3 (by omega) lambda x hden]
  simp only [theorem1OneColumnNuttallQ]
  rw [hratio, norm_nuttallQ32_eq_sq_mul_radialTail a b ha.ne' hb,
    hnormzero]
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha.ne'
  field_simp [ha2]

end

end JinWishart
