import JinWishartFormalization.Theorem1ThreeRowsActualCDF
import JinWishartFormalization.Theorem2SingleColumnAnyRows
import JinWishartFormalization.ThreeRowMeanNorm

/-!
# Theorem 1 and Theorem 2 for a `3 × 1` mean, with Frobenius noncentrality

The model-facing CDF theorem is stated using the norm of the encoded real
mean. The norm identity below replaces that auxiliary parameter by the
paper's natural one-column parameter `lambda = ∑ i, ‖M i 0‖²`.
-/

open MeasureTheory ProbabilityTheory Set

namespace JinWishart

noncomputable section

private theorem threeRowMeanEnergy_hmean
    (M : Matrix (Fin 3) (Fin 1) ℂ) :
    ‖threeRowSampleToFin6 (complexSampleMean M)‖ ^ 2 =
      2 * ∑ i : Fin 3, ‖M i 0‖ ^ 2 :=
  threeRowSampleToFin6_mean_norm_sq_eq_twice_frobenius M

/-- Theorem 1 `(s,t,L)=(1,3,1)` candidate equals the actual CDF, with the
noncentrality parameter written directly as the squared Frobenius norm of
the complex `3 × 1` mean. -/
theorem theorem1ThreeRowsOneColumnCandidate_eq_actualCDF_frobenius
    (M : Matrix (Fin 3) (Fin 1) ℂ) (x : ℝ)
    (hEnergy : 0 < ∑ i : Fin 3, ‖M i 0‖ ^ 2) (hx : 0 ≤ x) :
    theorem1CdfCandidate 1 3 1 (by omega) (by omega)
        (fun _ : Fin 1 => ∑ i : Fin 3, ‖M i 0‖ ^ 2) x =
      cdf ((stdGaussian (ComplexSample (m := 3) (n := 1))).map
        (complexNoncentralSampleSmallestEigenvalue M (by norm_num))) x := by
  apply theorem1ThreeRowsOneColumnCandidate_eq_actualCDF
    M _ x hEnergy hx
  simpa using threeRowMeanEnergy_hmean M

/-- Over a `1 × 1` Gram matrix the largest and smallest eigenvalue are the
same statistic. Theorem 2's `(1,3,1)` candidate therefore also equals the
actual CDF, now with `lambda` expressed as the Frobenius energy of `M`. -/
theorem theorem2ThreeRowsOneColumnCandidate_eq_actualCDF_frobenius
    (M : Matrix (Fin 3) (Fin 1) ℂ) (x : ℝ)
    (hEnergy : 0 < ∑ i : Fin 3, ‖M i 0‖ ^ 2) (hx : 0 ≤ x) :
    theorem2CdfCandidate 1 3 1 (by omega) (by omega)
        (fun _ : Fin 1 => ∑ i : Fin 3, ‖M i 0‖ ^ 2) x =
      cdf ((stdGaussian (ComplexSample (m := 3) (n := 1))).map
        (complexNoncentralSampleSmallestEigenvalue M (by norm_num))) x := by
  let lambda : ℝ := ∑ i : Fin 3, ‖M i 0‖ ^ 2
  let a : ℝ := Real.sqrt (2 * lambda)
  let b : ℝ := Real.sqrt (2 * x)
  have hlambda : 0 < lambda := by simpa [lambda] using hEnergy
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
  have htailNonneg : 0 ≤ ∫ r in Ioi b,
      noncentralChiSixRadialSeriesKernel a r :=
    setIntegral_nonneg measurableSet_Ioi fun r hr =>
      noncentralChiSixRadialSeriesKernel_nonneg a r
        (le_of_lt (lt_of_le_of_lt hb hr))
  have htailLe : ∫ r in Ioi b,
      noncentralChiSixRadialSeriesKernel a r ≤ 1 := by
    calc
      (∫ r in Ioi b, noncentralChiSixRadialSeriesKernel a r) ≤
          ∫ r in Ioi (0 : ℝ), noncentralChiSixRadialSeriesKernel a r := by
        apply setIntegral_mono_set
          (integrableOn_noncentralChiSixRadialSeriesKernel a) ?_
          (Ioi_subset_Ioi hb).eventuallySubset
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        exact noncentralChiSixRadialSeriesKernel_nonneg a r (le_of_lt hr)
      _ = 1 := noncentralChiSixRadialSeriesKernel_integral_eq_one a
  have hQb : nuttallQ 3 2 a b =
      ((a ^ 2 * ∫ r in Ioi b,
        noncentralChiSixRadialSeriesKernel a r : ℝ) : ℂ) :=
    nuttallQ32_eq_ofReal_scaledRadialTail a b ha.ne' hb
  have hdiff : nuttallQ 3 2 a 0 - nuttallQ 3 2 a b =
      ((a ^ 2 * (1 - ∫ r in Ioi b,
        noncentralChiSixRadialSeriesKernel a r) : ℝ) : ℂ) := by
    rw [hqzero, hQb]
    push_cast
    ring
  have hdiffNonneg : 0 ≤ a ^ 2 * (1 - ∫ r in Ioi b,
      noncentralChiSixRadialSeriesKernel a r) :=
    mul_nonneg (sq_nonneg a) (sub_nonneg.mpr htailLe)
  have hnormDiff : ‖nuttallQ 3 2 a 0 - nuttallQ 3 2 a b‖ =
      a ^ 2 * (1 - ∫ r in Ioi b,
        noncentralChiSixRadialSeriesKernel a r) := by
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hdiffNonneg]
  have hnormQb : ‖nuttallQ 3 2 a b‖ =
      a ^ 2 * ∫ r in Ioi b,
        noncentralChiSixRadialSeriesKernel a r := by
    rw [hQb, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (sq_nonneg a) htailNonneg)]
  have hcandidateEq :
      ‖nuttallQ 3 2 a 0 - nuttallQ 3 2 a b‖ /
          ‖nuttallQ 3 2 a 0‖ =
        1 - ‖nuttallQ 3 2 a b‖ / ‖nuttallQ 3 2 a 0‖ := by
    rw [hnormDiff, hnormQb, hnormzero]
    field_simp [ne_of_gt (sq_pos_of_ne_zero ha.ne')]
  have hT2 := theorem2OneColumnCandidate_eq_normalizedNuttallQIncrement
    3 (by omega) lambda x hden
  have hT1 := theorem1OneColumnCandidate_eq_normalizedNuttallQ
    3 (by omega) lambda x hden
  have hT1actual := theorem1ThreeRowsOneColumnCandidate_eq_actualCDF
    M lambda x hlambda hx (by
      simpa [lambda] using threeRowMeanEnergy_hmean M)
  calc
    theorem2CdfCandidate 1 3 1 (by omega) (by omega)
        (fun _ : Fin 1 => ∑ i : Fin 3, ‖M i 0‖ ^ 2) x =
        theorem1CdfCandidate 1 3 1 (by omega) (by omega)
          (fun _ : Fin 1 => lambda) x := by
      rw [show (∑ i : Fin 3, ‖M i 0‖ ^ 2) = lambda by rfl, hT2, hT1]
      exact hcandidateEq
    _ = cdf ((stdGaussian (ComplexSample (m := 3) (n := 1))).map
          (complexNoncentralSampleSmallestEigenvalue M (by norm_num))) x :=
      hT1actual

end

end JinWishart
