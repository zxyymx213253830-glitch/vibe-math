import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Weighted interval averages

Elementary scaling identities for the radial average
`(2 / R^2) ∫₀ᴿ r g(r) dr`.  They isolate the analytic core of the
small-threshold scalar noncentral calculation.
-/

open Filter MeasureTheory Set Topology

namespace JinWishart

noncomputable section

/-- Scaling a radius-weighted interval integral to the unit interval. -/
theorem weightedIntervalIntegral_scale (g : ℝ → ℝ) (R : ℝ) :
    R * (∫ s in (0 : ℝ)..1, (s * R) * g (s * R)) =
      ∫ r in (0 : ℝ)..R, r * g r := by
  simpa [smul_eq_mul] using
    (intervalIntegral.smul_integral_comp_mul_right
      (fun r : ℝ => r * g r) R (a := (0 : ℝ)) (b := 1))

/-- For nonzero radius, the normalized weighted average is the integral of
the rescaled integrand on the fixed unit interval. -/
theorem normalized_weightedIntervalIntegral_scale
    (g : ℝ → ℝ) (R : ℝ) (hR : R ≠ 0) :
    (2 / R ^ 2) * (∫ r in (0 : ℝ)..R, r * g r) =
      2 * ∫ s in (0 : ℝ)..1, s * g (s * R) := by
  rw [← weightedIntervalIntegral_scale g R]
  have hfactor :
      (∫ s in (0 : ℝ)..1, (s * R) * g (s * R)) =
        R * ∫ s in (0 : ℝ)..1, s * g (s * R) := by
    calc
      _ = ∫ s in (0 : ℝ)..1, R * (s * g (s * R)) := by
        apply intervalIntegral.integral_congr
        intro s _
        ring
      _ = _ := by rw [intervalIntegral.integral_const_mul]
  rw [hfactor]
  field_simp

/-- The unit-interval normalization of the radial weight. -/
theorem normalized_unit_interval_weight :
    2 * (∫ s in (0 : ℝ)..1, s) = 1 := by
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    intro x _
    convert (hasDerivAt_id' x).pow 2 using 1 <;> ring
  have hint : IntervalIntegrable (fun x : ℝ => 2 * x) volume 0 1 :=
    (continuous_const.mul continuous_id).intervalIntegrable 0 1
  calc
    2 * (∫ s in (0 : ℝ)..1, s) = ∫ s in (0 : ℝ)..1, 2 * s := by
      rw [intervalIntegral.integral_const_mul]
    _ = (fun y : ℝ => y ^ 2) 1 - (fun y : ℝ => y ^ 2) 0 := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    _ = 1 := by norm_num

/-- Continuity at zero gives uniform convergence of the rescaled integrands
on the fixed unit interval. -/
theorem weighted_rescaled_tendstoUniformlyOn
    {g : ℝ → ℝ} (hg : Continuous g) :
    TendstoUniformlyOn (fun R s : ℝ => s * g (s * R))
      (fun s : ℝ => s * g 0) (𝓝 0) (Icc (0 : ℝ) 1) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  rcases Metric.continuousAt_iff.mp hg.continuousAt ε hε with ⟨δ, hδ, hcont⟩
  filter_upwards [Metric.eventually_nhds_iff.2 ⟨δ, hδ, fun R hR => hR⟩] with R hR
  intro s hs
  have hs0 : 0 ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have harg : dist (s * R) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_mul, abs_of_nonneg hs0]
    calc
      s * |R| ≤ 1 * |R| := mul_le_mul_of_nonneg_right hs1 (abs_nonneg R)
      _ = |R| := one_mul _
      _ = dist R 0 := by simp [Real.dist_eq]
      _ < δ := hR
  have hgR := hcont harg
  rw [Real.dist_eq] at hgR ⊢
  calc
    |s * g 0 - s * g (s * R)| = |s| * |g (s * R) - g 0| := by
      rw [abs_sub_comm]
      rw [← abs_mul]
      congr 1
      ring
    _ = s * |g (s * R) - g 0| := by rw [abs_of_nonneg hs0]
    _ ≤ 1 * |g (s * R) - g 0| :=
      mul_le_mul_of_nonneg_right hs1 (abs_nonneg _)
    _ = |g (s * R) - g 0| := one_mul _
    _ < ε := hgR

/-- Integrating the uniformly convergent rescaled integrands gives the
fixed-interval weighted-average limit. -/
theorem weighted_rescaled_integral_tendsto
    {g : ℝ → ℝ} (hg : Continuous g) :
    Tendsto (fun R : ℝ => 2 * ∫ s in (0 : ℝ)..1, s * g (s * R))
      (𝓝 0) (𝓝 (g 0)) := by
  have hcont : ∀ᶠ R : ℝ in (𝓝 0),
      ContinuousOn (fun s : ℝ => s * g (s * R)) (uIcc (0 : ℝ) 1) := by
    filter_upwards [] with R
    exact (continuous_id.mul (hg.comp
      (continuous_id.mul continuous_const))).continuousOn
  have huniform : TendstoUniformlyOn (fun R s : ℝ => s * g (s * R))
      (fun s : ℝ => s * g 0) (𝓝 0) (uIcc (0 : ℝ) 1) := by
    simpa [uIcc_of_le] using weighted_rescaled_tendstoUniformlyOn hg
  have hint := TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
    (μ := volume) hcont huniform
  have hmul : Tendsto (fun R : ℝ => (2 : ℝ) *
      (∫ s in (0 : ℝ)..1, s * g (s * R))) (𝓝 0)
      (𝓝 ((2 : ℝ) * ∫ s in (0 : ℝ)..1, s * g 0)) :=
    tendsto_const_nhds.mul hint
  have hvalue : (2 : ℝ) * ∫ s in (0 : ℝ)..1, s * g 0 = g 0 := by
    rw [intervalIntegral.integral_mul_const]
    calc
      2 * ((∫ s in (0 : ℝ)..1, s) * g 0) =
          (2 * ∫ s in (0 : ℝ)..1, s) * g 0 := by ring
      _ = g 0 := by rw [normalized_unit_interval_weight, one_mul]
  rw [hvalue] at hmul
  exact hmul

/-- A continuous radial factor has the expected normalized weighted-average
limit as the radius decreases to zero. -/
theorem normalized_weightedIntervalIntegral_tendsto
    {g : ℝ → ℝ} (hg : Continuous g) :
    Tendsto (fun R : ℝ => (2 / R ^ 2) *
      (∫ r in (0 : ℝ)..R, r * g r)) (𝓝[>] 0) (𝓝 (g 0)) := by
  have hlim := tendsto_nhdsWithin_of_tendsto_nhds
    (weighted_rescaled_integral_tendsto hg) (s := Ioi (0 : ℝ))
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with R hR
  exact (normalized_weightedIntervalIntegral_scale g R (ne_of_gt hR)).symm

end

end JinWishart
