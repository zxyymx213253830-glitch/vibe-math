import JinWishartFormalization.TwoRowSmallOutageAsymptotic
import JinWishartFormalization.MIMOPerformance

/-!
# Positive-scale outage rescaling for the actual two-row one-column model

This module converts the real `2 × 1` Gram-eigenvalue outage event to its CDF,
then transfers the already-proved small-threshold limit to a large-scale limit.
The scale is an abstract positive multiplier; no identification with the paper's
`(K+1)P/r` is made here.
-/

open Filter Matrix MeasureTheory ProbabilityTheory Topology

namespace JinWishart

/-- A second-order version of the small-threshold-to-large-scale transfer. -/
theorem smallThresholdRatioSq_to_highScale
    (F : ℝ → ℝ) (L γ : ℝ) (hγ : 0 < γ)
    (hF : Tendsto (fun x : ℝ => F x / x ^ 2) (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun c : ℝ => c ^ 2 * F (γ / c)) atTop (𝓝 (γ ^ 2 * L)) := by
  have hinv : Tendsto (fun c : ℝ => c⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_nhdsGT_zero.mono_right nhdsWithin_le_nhds
  have hRzero : Tendsto (fun c : ℝ => γ / c) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds (x := γ)).mul hinv
  have hRpos : ∀ᶠ c : ℝ in atTop, γ / c ∈ Set.Ioi 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
    exact div_pos hγ hc
  have hR : Tendsto (fun c : ℝ => γ / c) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hRzero, hRpos⟩
  have hcomp := hF.comp hR
  have hmul : Tendsto (fun c : ℝ => γ ^ 2 * (F (γ / c) / (γ / c) ^ 2))
      atTop (𝓝 (γ ^ 2 * L)) := by
    exact tendsto_const_nhds.mul hcomp
  apply hmul.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hγ0 : γ ≠ 0 := ne_of_gt hγ
  field_simp [hc0, hγ0]

private theorem statisticCDF_to_actualCDF
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (φ : Ω → ℝ) (hφ : Measurable φ) (x : ℝ) :
    (statisticCDF μ φ x).toReal = cdf (μ.map φ) x := by
  unfold statisticCDF
  rw [cdf_eq_real, measureReal_def]
  rw [Measure.map_apply hφ measurableSet_Iic]
  rfl

/-- For an actual `2 × 1` shifted complex Gaussian Gram statistic, weak outage
at any positive SNR scale is exactly its CDF at the divided threshold. -/
theorem twoRowWeakOutage_to_actualCDF
    (M : Matrix (Fin 2) (Fin 1) ℂ) (scale threshold : ℝ)
    (hscale : 0 < scale) :
    (weakOutageProbability
      (stdGaussian (ComplexSample (m := 2) (n := 1)))
      (complexNoncentralSampleSmallestEigenvalue M (by norm_num)) scale threshold).toReal =
      cdf ((stdGaussian (ComplexSample (m := 2) (n := 1))).map
        (complexNoncentralSampleSmallestEigenvalue M (by norm_num)))
        (threshold / scale) := by
  rw [weakOutageProbability_eq_statisticCDF _ _ scale threshold hscale]
  exact statisticCDF_to_actualCDF _ _
    (measurable_complexNoncentralSampleSmallestEigenvalue M (by norm_num)) _

/-- The actual `2 × 1` weak outage probability has a quadratic large-scale
asymptotic at fixed positive threshold. The mean-dependent coefficient is the
one from the actual small-threshold CDF theorem. -/
theorem twoRowWeakOutage_highScale_limit
    (M : Matrix (Fin 2) (Fin 1) ℂ) (threshold : ℝ) (hthreshold : 0 < threshold) :
    Tendsto (fun scale : ℝ => scale ^ 2 *
      (weakOutageProbability
        (stdGaussian (ComplexSample (m := 2) (n := 1)))
        (complexNoncentralSampleSmallestEigenvalue M (by norm_num)) scale threshold).toReal)
      atTop (𝓝 (threshold ^ 2 *
        ((1 / 2) * Real.exp
          (-(‖complexSampleMean M‖ ^ 2 / 2))))) := by
  let F : ℝ → ℝ := fun x =>
    cdf ((stdGaussian (ComplexSample (m := 2) (n := 1))).map
      (complexNoncentralSampleSmallestEigenvalue M (by norm_num))) x
  have hF : Tendsto (fun x : ℝ => F x / x ^ 2) (𝓝[>] 0)
      (𝓝 ((1 / 2) * Real.exp
        (-(‖complexSampleMean M‖ ^ 2 / 2)))) := by
    simpa [F] using
      noncentralTwoRowCDF_div_tendsto_exp_neg_noncentrality_half_anyMean M
  have hscaled := smallThresholdRatioSq_to_highScale F
    ((1 / 2) * Real.exp (-(‖complexSampleMean M‖ ^ 2 / 2)))
    threshold hthreshold hF
  apply hscaled.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with scale hscale
  rw [twoRowWeakOutage_to_actualCDF M scale threshold hscale]

end JinWishart
