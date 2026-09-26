import JinWishartFormalization.ScalarNoncentralSmallXLimit

/-!
# Scalar noncentral high-scale outage asymptotic

The `1×1` small-threshold CDF limit transfers to a high-scale outage limit.
This is an application of the scalar special case, not the paper's general
MIMO outage formula.
-/

open Filter Matrix MeasureTheory ProbabilityTheory Topology

namespace JinWishart

/-- A small-threshold first-order CDF limit transfers to a high-SNR scale
limit for any positive fixed outage threshold. -/
theorem smallThresholdRatio_to_highScale
    (F : ℝ → ℝ) (L γ : ℝ) (hγ : 0 < γ)
    (hF : Tendsto (fun x : ℝ => F x / x) (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun c : ℝ => c * F (γ / c)) atTop (𝓝 (γ * L)) := by
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
  have hmul : Tendsto (fun c : ℝ => γ * (F (γ / c) / (γ / c)))
      atTop (𝓝 (γ * L)) := by
    exact tendsto_const_nhds.mul hcomp
  apply hmul.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hγ0 : γ ≠ 0 := ne_of_gt hγ
  field_simp [hc0, hγ0]

/-- For the actual scalar noncentral complex Wishart CDF, the weak outage
probability at threshold `γ` has leading high-scale coefficient
`γ exp(-‖M₀₀‖²)`. The scale `c` multiplies the unique Gram eigenvalue. -/
theorem scalarNoncentral_outage_highScale_limit
    (M : Matrix (Fin 1) (Fin 1) ℂ) (γ : ℝ) (hγ : 0 < γ) :
    Tendsto (fun c : ℝ => c *
      cdf ((stdGaussian (ComplexSample (m := 1) (n := 1))).map
        (complexNoncentralSampleSmallestEigenvalue M (by norm_num))) (γ / c))
      atTop (𝓝 (γ * Real.exp (-‖M 0 0‖ ^ 2))) := by
  exact smallThresholdRatio_to_highScale _ _ γ hγ
    (noncentralScalarCDF_div_tendsto_exp_neg_noncentrality M)

end JinWishart
