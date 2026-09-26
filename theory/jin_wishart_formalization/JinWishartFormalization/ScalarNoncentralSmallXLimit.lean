import JinWishartFormalization.ScalarNoncentralSmallX
import JinWishartFormalization.WeightedIntervalAverage

/-!
# Scalar noncentral small-threshold asymptotic

The `1 × 1` noncentral complex Wishart CDF has leading term
`exp (-||M₀₀||²) x` as `x` decreases to zero.
-/

open Filter Matrix MeasureTheory ProbabilityTheory Set Topology

namespace JinWishart

noncomputable section

/-- The scalar noncentral Wishart CDF has the Theorem 4 leading coefficient
at the hard edge. -/
theorem noncentralScalarCDF_div_tendsto_exp_neg_noncentrality
    (M : Matrix (Fin 1) (Fin 1) ℂ) :
    Tendsto (fun x : ℝ =>
      cdf ((stdGaussian (ComplexSample (m := 1) (n := 1))).map
        (complexNoncentralSampleSmallestEigenvalue M (by norm_num))) x / x)
      (𝓝[>] 0) (𝓝 (Real.exp (-‖M 0 0‖ ^ 2))) := by
  let g : ℝ → ℝ := riceRadialFactor ‖complexSampleMean M‖
  have hg : Continuous g := continuous_riceRadialFactor _
  have hR : Tendsto (fun x : ℝ => Real.sqrt (2 * x))
      (𝓝[>] 0) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · apply tendsto_nhdsWithin_of_tendsto_nhds
      have hbase : ContinuousAt (fun x : ℝ => 2 * x) 0 := by fun_prop
      change Tendsto ((fun y : ℝ => Real.sqrt y) ∘ fun x : ℝ => 2 * x)
        (𝓝 0) (𝓝 0)
      simpa only [mul_zero, Real.sqrt_zero] using
        (Real.continuous_sqrt.continuousAt.tendsto.comp hbase.tendsto)
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact Real.sqrt_pos.2 (mul_pos (by norm_num) hx)
  have havg := (normalized_weightedIntervalIntegral_tendsto hg).comp hR
  have hpoint : ∀ᶠ x : ℝ in (𝓝[>] 0),
      cdf ((stdGaussian (ComplexSample (m := 1) (n := 1))).map
        (complexNoncentralSampleSmallestEigenvalue M (by norm_num))) x / x =
        (2 / (Real.sqrt (2 * x)) ^ 2) *
          (∫ r in (0 : ℝ)..Real.sqrt (2 * x), r * g r) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hCDF := noncentralScalarCDF_eq_radius_factorIntegral M x hx.le
    have hsqrt : (Real.sqrt (2 * x)) ^ 2 = 2 * x :=
      Real.sq_sqrt (mul_nonneg (by norm_num) hx.le)
    change cdf ((stdGaussian (ComplexSample (m := 1) (n := 1))).map
      (complexNoncentralSampleSmallestEigenvalue M (by norm_num))) x =
      ∫ r in Ioc (0 : ℝ) (Real.sqrt (2 * x)), r * g r at hCDF
    rw [hCDF, ← intervalIntegral.integral_of_le (Real.sqrt_nonneg _)]
    field_simp
    rw [hsqrt]
    ring
  have hfactor : g 0 = Real.exp (-‖M 0 0‖ ^ 2) :=
    riceRadialFactor_zero_eq_exp_neg_noncentrality M
  rw [← hfactor]
  apply havg.congr'
  filter_upwards [hpoint] with x hx
  exact hx.symm

end

end JinWishart
