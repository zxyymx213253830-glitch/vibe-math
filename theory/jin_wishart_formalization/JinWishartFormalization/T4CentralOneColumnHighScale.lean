import JinWishartFormalization.T4CentralOneColumnAnyRows
import JinWishartFormalization.MIMOPerformance

/-!
# High-scale outage asymptotics for the central one-column model

This is an application of the proved Theorem 4 hard-edge limit in the central
`m × 1` model.  It converts the small-threshold asymptotic of the actual least
Gram eigenvalue into a large-scale weak-outage asymptotic at a fixed positive
threshold.  It does not assert the general multi-column or noncentral formula.
-/

open Filter Matrix MeasureTheory ProbabilityTheory Set Topology

namespace JinWishart

noncomputable section

/-- A hard-edge CDF ratio of order `m` yields a high-scale limit after the
threshold is divided by the scale. -/
theorem smallThresholdRatioPow_to_highScale
    (F : ℝ → ℝ) (L γ : ℝ) (m : ℕ) (hγ : 0 < γ)
    (hF : Tendsto (fun x : ℝ => F x / x ^ m) (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun c : ℝ => c ^ m * F (γ / c)) atTop (𝓝 (γ ^ m * L)) := by
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
  have hmul : Tendsto (fun c : ℝ => γ ^ m * (F (γ / c) / (γ / c) ^ m))
      atTop (𝓝 (γ ^ m * L)) :=
    tendsto_const_nhds.mul hcomp
  apply hmul.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hγ0 : γ ≠ 0 := ne_of_gt hγ
  rw [div_pow]
  field_simp [hc0, hγ0]

private theorem statisticCDF_to_actualCDF
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (φ : Ω → ℝ) (hφ : Measurable φ) (x : ℝ) :
    (statisticCDF μ φ x).toReal = cdf (μ.map φ) x := by
  unfold statisticCDF
  rw [cdf_eq_real, measureReal_def]
  rw [Measure.map_apply hφ measurableSet_Iic]
  rfl

/-- In the actual central `m × 1` sample, weak outage at positive scale is the
smallest-eigenvalue CDF evaluated at the divided threshold. -/
private theorem centralOneColumnWeakOutage_to_actualCDF
    (m : ℕ) (hm : 0 < m) (scale threshold : ℝ) (hscale : 0 < scale) :
    (weakOutageProbability
      (stdGaussian (ComplexSample (m := m) (n := 1)))
      (complexNoncentralSampleSmallestEigenvalue
        (0 : Matrix (Fin m) (Fin 1) ℂ) (by norm_num)) scale threshold).toReal =
      cdf ((stdGaussian (ComplexSample (m := m) (n := 1))).map
        (complexNoncentralSampleSmallestEigenvalue
          (0 : Matrix (Fin m) (Fin 1) ℂ) (by norm_num))) (threshold / scale) := by
  rw [weakOutageProbability_eq_statisticCDF _ _ scale threshold hscale]
  exact statisticCDF_to_actualCDF _ _
    (measurable_complexNoncentralSampleSmallestEigenvalue
      (0 : Matrix (Fin m) (Fin 1) ℂ) (by norm_num)) _

/-- **Central one-column high-scale outage law.** For `m > 0`, the actual weak
outage probability of the least eigenvalue of the central `m × 1` complex Gram
sample decays with diversity exponent `m`; at fixed threshold `γ > 0`,
`scale^m · P(scale · λ_min ≤ γ) → γ^m/m!`. -/
theorem centralOneColumnWeakOutage_highScale_limit
    (m : ℕ) (hm : 0 < m) (γ : ℝ) (hγ : 0 < γ) :
    Tendsto (fun scale : ℝ => scale ^ m *
      (weakOutageProbability
        (stdGaussian (ComplexSample (m := m) (n := 1)))
        (complexNoncentralSampleSmallestEigenvalue
          (0 : Matrix (Fin m) (Fin 1) ℂ) (by norm_num)) scale γ).toReal)
      atTop (𝓝 (γ ^ m * (Nat.factorial m : ℝ)⁻¹)) := by
  let F : ℝ → ℝ := fun x =>
    cdf ((stdGaussian (ComplexSample (m := m) (n := 1))).map
      (complexNoncentralSampleSmallestEigenvalue
        (0 : Matrix (Fin m) (Fin 1) ℂ) (by norm_num))) x
  have hF : Tendsto (fun x : ℝ => F x / x ^ m) (𝓝[>] 0)
      (𝓝 ((Nat.factorial m : ℝ)⁻¹)) := by
    simpa [F] using centralOneColumnSmallestCDF_div_tendsto_factorial m hm
  have hscaled := smallThresholdRatioPow_to_highScale F
    ((Nat.factorial m : ℝ)⁻¹) γ m hγ hF
  apply hscaled.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with scale hscale
  rw [centralOneColumnWeakOutage_to_actualCDF m hm scale γ hscale]

end

end JinWishart
