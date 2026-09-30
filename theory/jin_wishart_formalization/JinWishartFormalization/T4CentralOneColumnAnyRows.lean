import JinWishartFormalization.WishartGamma

/-!
# Theorem 4: arbitrary-row central one-column hard-edge law

For every positive row count `m`, the actual smallest eigenvalue of a central
`m × 1` complex Gaussian Gram matrix has a Gamma(`m`, 1) law. This file
derives its exact hard-edge power and coefficient from that real model law.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace JinWishart

noncomputable section

private theorem powExpIntegral_rescale (k : ℕ) (x : ℝ) :
    (∫ u in (0 : ℝ)..x, u ^ k * Real.exp (-u)) =
      x ^ (k + 1) * ∫ s in (0 : ℝ)..1, s ^ k * Real.exp (-(s * x)) := by
  have hscale := intervalIntegral.smul_integral_comp_mul_right
    (fun u : ℝ => u ^ k * Real.exp (-u)) x (a := (0 : ℝ)) (b := 1)
  have hfactor : (∫ s in (0 : ℝ)..1,
      (s * x) ^ k * Real.exp (-(s * x))) =
      x ^ k * ∫ s in (0 : ℝ)..1, s ^ k * Real.exp (-(s * x)) := by
    calc
      _ = ∫ s in (0 : ℝ)..1, x ^ k * (s ^ k * Real.exp (-(s * x))) := by
        apply intervalIntegral.integral_congr
        intro s _
        change (s * x) ^ k * Real.exp (-(s * x)) = _
        rw [mul_pow]
        ring
      _ = _ := intervalIntegral.integral_const_mul ..
  calc
    _ = x * ∫ s in (0 : ℝ)..1, (s * x) ^ k * Real.exp (-(s * x)) := by
      simpa [smul_eq_mul] using hscale.symm
    _ = x ^ (k + 1) * ∫ s in (0 : ℝ)..1, s ^ k * Real.exp (-(s * x)) := by
      rw [hfactor]
      rw [pow_succ]
      ring

private theorem integral_pow_Ioc_unit (k : ℕ) :
    (∫ s in (0 : ℝ)..1, s ^ k) = (k + 1 : ℝ)⁻¹ := by
  rw [integral_pow]
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  norm_num

private theorem powerExponentialIntegral_tendsto (k : ℕ) :
    Tendsto (fun x : ℝ => ∫ s in (0 : ℝ)..1,
      s ^ k * Real.exp (-(s * x))) (𝓝 0)
      (𝓝 ((k + 1 : ℝ)⁻¹)) := by
  have huniform : TendstoUniformlyOn
      (fun x s : ℝ => s ^ k * Real.exp (-(s * x)))
      (fun s : ℝ => s ^ k) (𝓝 0) (Icc (0 : ℝ) 1) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp
      Real.continuous_exp.continuousAt ε hε
    filter_upwards [Metric.eventually_nhds_iff.mpr ⟨δ, hδ, fun x hx => hx⟩]
      with x hx
    intro s hs
    have hs0 : 0 ≤ s := hs.1
    have hs1 : s ≤ 1 := hs.2
    have harg : dist (-(s * x)) 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_neg, abs_mul, abs_of_nonneg hs0]
      calc
        s * |x| ≤ 1 * |x| := mul_le_mul_of_nonneg_right hs1 (abs_nonneg x)
        _ = |x| := one_mul _
        _ = dist x 0 := by simp [Real.dist_eq]
        _ < δ := hx
    have hexp := hcont harg
    rw [Real.dist_eq] at hexp ⊢
    have hpow0 : 0 ≤ s ^ k := pow_nonneg hs0 _
    have hpow1 : s ^ k ≤ 1 := by
      exact pow_le_one₀ hs0 hs1
    have hdiff : s ^ k - s ^ k * Real.exp (-(s * x)) =
        s ^ k * (1 - Real.exp (-(s * x))) := by ring
    calc
      |s ^ k - s ^ k * Real.exp (-(s * x))| =
          s ^ k * |Real.exp (-(s * x)) - 1| := by
            rw [hdiff, abs_mul, abs_of_nonneg hpow0, abs_sub_comm]
      _ ≤ 1 * |Real.exp (-(s * x)) - 1| :=
        mul_le_mul_of_nonneg_right hpow1 (abs_nonneg _)
      _ = |Real.exp (-(s * x)) - 1| := one_mul _
      _ < ε := by simpa using hexp
  have hcont : ∀ᶠ x : ℝ in 𝓝 0,
      ContinuousOn (fun s : ℝ => s ^ k * Real.exp (-(s * x)))
        (uIcc (0 : ℝ) 1) := by
    filter_upwards [] with x
    exact ((continuous_id.pow k).mul
      (Real.continuous_exp.comp (continuous_neg.comp
        (continuous_id.mul continuous_const)))).continuousOn
  have huniform' : TendstoUniformlyOn
      (fun x s : ℝ => s ^ k * Real.exp (-(s * x)))
      (fun s : ℝ => s ^ k) (𝓝 0) (uIcc (0 : ℝ) 1) := by
    simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using huniform
  have hint := TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
    (μ := volume) hcont huniform'
  simpa [integral_pow_Ioc_unit] using hint

/-- **Theorem 4, central one-column case, arbitrary row count.** For every
positive integer `m`, the actual smallest-eigenvalue CDF of the central
`m × 1` complex Wishart model satisfies `F(x)/x^m → 1/m!` at zero from the
right. This is the paper's diversity exponent `(s-k+1)(t-k+1)` at `s=k=1`,
`t=m`, with the exact central coefficient. -/
theorem centralOneColumnSmallestCDF_div_tendsto_factorial (m : ℕ) (hm : 0 < m) :
    Tendsto (fun x : ℝ =>
      cdf ((stdGaussian (ComplexSample (m := m) (n := 1))).map
        (complexNoncentralSampleSmallestEigenvalue
          (0 : Matrix (Fin m) (Fin 1) ℂ) (by norm_num))) x / x ^ m)
      (𝓝[>] 0) (𝓝 ((Nat.factorial m : ℝ)⁻¹)) := by
  let k := m - 1
  have hk : 0 < k + 1 := by dsimp [k]; omega
  have hbase := powerExponentialIntegral_tendsto k
  have hright := tendsto_nhdsWithin_of_tendsto_nhds hbase
    (s := Set.Ioi (0 : ℝ))
  have hfact : (Nat.factorial m : ℝ) =
      (m : ℝ) * (Nat.factorial k : ℝ) := by
    have hn : m - 1 + 1 = m := Nat.sub_add_cancel hm
    have hnat : m.factorial = m * (m - 1).factorial := by
      calc
        m.factorial = (m - 1 + 1).factorial := by rw [hn]
        _ = (m - 1 + 1) * (m - 1).factorial := Nat.factorial_succ _
        _ = m * (m - 1).factorial := by rw [hn]
    exact_mod_cast hnat
  have hlimConst : (Nat.factorial k : ℝ)⁻¹ * (k + 1 : ℝ)⁻¹ =
      (Nat.factorial m : ℝ)⁻¹ := by
    have hmkN : k + 1 = m := by dsimp [k]; omega
    have hmk : (k + 1 : ℝ) = m := by exact_mod_cast hmkN
    rw [hfact, hmk]
    field_simp
  have hpoint : ∀ᶠ x : ℝ in 𝓝[>] 0,
      cdf ((stdGaussian (ComplexSample (m := m) (n := 1))).map
        (complexNoncentralSampleSmallestEigenvalue
          (0 : Matrix (Fin m) (Fin 1) ℂ) (by norm_num))) x / x ^ m =
      (Nat.factorial k : ℝ)⁻¹ *
        ∫ s in (0 : ℝ)..1, s ^ k * Real.exp (-(s * x)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxpos : 0 < x := hx
    have hxnonneg : 0 ≤ x := le_of_lt hxpos
    have hCDF : cdf ((stdGaussian (ComplexSample (m := m) (n := 1))).map
        (complexNoncentralSampleSmallestEigenvalue
          (0 : Matrix (Fin m) (Fin 1) ℂ) (by norm_num))) x =
        (Nat.factorial k : ℝ)⁻¹ *
          ∫ u in (0 : ℝ)..x, u ^ k * Real.exp (-u) := by
      rw [centralColumnSmallestEigenvalue_map_eq_gammaMeasure hm,
        cdf_gammaMeasure_nat_eq_lowerGamma m hm x hxnonneg]
    have hscaled :
        (∫ u in (0 : ℝ)..x, u ^ k * Real.exp (-u)) =
          x ^ (k + 1) * ∫ s in (0 : ℝ)..1,
            s ^ k * Real.exp (-(x * s)) := by
      simpa [mul_comm] using powExpIntegral_rescale k x
    have hkm : k + 1 = m := by dsimp [k]; omega
    have hpow : x ^ (k + 1) = x ^ m := by rw [hkm]
    rw [hCDF, hscaled, hpow]
    have hxn : x ^ m ≠ 0 := pow_ne_zero _ (ne_of_gt hxpos)
    field_simp [hxn]
  have hcoef : Tendsto (fun _ : ℝ => (Nat.factorial k : ℝ)⁻¹)
      (𝓝[>] 0) (𝓝 ((Nat.factorial k : ℝ)⁻¹)) := tendsto_const_nhds
  have hlim := hcoef.mul hright
  have hlim' : Tendsto (fun x : ℝ =>
      (Nat.factorial k : ℝ)⁻¹ *
        ∫ s in (0 : ℝ)..1, s ^ k * Real.exp (-(s * x)))
      (𝓝[>] 0) (𝓝 ((Nat.factorial m : ℝ)⁻¹)) := by
    simpa [hlimConst] using hlim
  have hpoint' : (fun x : ℝ => (Nat.factorial k : ℝ)⁻¹ *
        ∫ s in (0 : ℝ)..1, s ^ k * Real.exp (-(s * x))) =ᶠ[𝓝[>] 0]
      (fun x => cdf ((stdGaussian (ComplexSample (m := m) (n := 1))).map
        (complexNoncentralSampleSmallestEigenvalue
          (0 : Matrix (Fin m) (Fin 1) ℂ) (by norm_num))) x / x ^ m) := by
    filter_upwards [hpoint] with x hx
    exact hx.symm
  exact hlim'.congr' hpoint'

end

end JinWishart
