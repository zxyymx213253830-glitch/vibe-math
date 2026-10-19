import JinWishartFormalization.CentralMinimumAllShapesDiversity

/-!
# Scalar covariance and high-SNR minimum diversity

Codex. v is CN covariance; samples are multiplied by sqrt(v).
[需人工审查] Variance, outage threshold and asymptotic interpretation.
-/
open Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace JinWishart
noncomputable section

def actualCentralCovarianceMinimumCDF (d n : ℕ) (v x : ℝ) : ℝ :=
  (stdGaussian (ComplexSample (m := d+(n+1)) (n := n+1))).real
    {z | centralGaussianSampleMinimum (d+(n+1)) (n+1) (Nat.succ_pos n) (Real.sqrt v • z) ≤ x}

theorem actualCentralCovarianceMinimumCDF_eq (d n : ℕ) (v : ℝ) (hv : 0 < v) (x : ℝ) :
    actualCentralCovarianceMinimumCDF d n v x = actualCentralMinimumCDF d n (x/v) := by
  unfold actualCentralCovarianceMinimumCDF actualCentralMinimumCDF
  congr 1
  ext z
  simp only [Set.mem_setOf_eq,
    centralGaussianSampleMinimum_scale _ _ _ (Real.sqrt v) (Real.sqrt_pos.mpr hv),
    Real.sq_sqrt hv.le]
  rw [le_div_iff₀ hv,mul_comm]

theorem actualCentralCovarianceMinimumCDF_local_bounds (d n : ℕ) (v : ℝ) (hv : 0 < v)
    (x : ℝ) (hx : 0 < x) (hxv : x ≤ v) :
    (Real.exp (-1)/(Nat.factorial (d+1) : ℝ)/v^(d+1))*x^(d+1) ≤
        actualCentralCovarianceMinimumCDF d n v x ∧
    actualCentralCovarianceMinimumCDF d n v x ≤
      (((n+1 : ℕ) : ℝ)^(d+2)/(Nat.factorial (d+1) : ℝ)/v^(d+1))*x^(d+1) := by
  rw [actualCentralCovarianceMinimumCDF_eq d n v hv]
  have h := actualCentralMinimumCDF_all_local_power_bounds d n (x/v)
    (div_pos hx hv) ((div_le_one hv).mpr hxv)
  rw [div_pow] at h
  constructor
  · convert h.1 using 1 <;> ring
  · convert h.2 using 1 <;> ring

theorem actualCentralCovarianceMinimumCDF_diversity (d n : ℕ) (v : ℝ) (hv : 0 < v) :
    Tendsto (fun x : ℝ => Real.log (actualCentralCovarianceMinimumCDF d n v x)/Real.log x)
      (𝓝[>] 0) (𝓝 ((d+1 : ℕ) : ℝ)) := by
  apply tendsto_log_ratio_of_power_bounds _ (d+1)
    (Real.exp (-1)/(Nat.factorial (d+1) : ℝ)/v^(d+1))
    (((n+1 : ℕ) : ℝ)^(d+2)/(Nat.factorial (d+1) : ℝ)/v^(d+1))
  · positivity
  · positivity
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hv).filter_mono nhdsWithin_le_nhds] with x hx hxv
    exact ⟨hx,actualCentralCovarianceMinimumCDF_local_bounds d n v hv x hx hxv.le⟩

theorem tendsto_log_ratio_inverse_threshold (f : ℝ → ℝ) (a : ℝ)
    (hf : Tendsto (fun x => Real.log (f x)/Real.log x) (𝓝[>] 0) (𝓝 a))
    (b : ℝ) (hb : 0 < b) :
    Tendsto (fun r : ℝ => Real.log (f (b/r))/Real.log r) atTop (𝓝 (-a)) := by
  have ht : Tendsto (fun r : ℝ => b/r) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_id.const_div_atTop b,?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact div_pos hb hr
  have hz := Real.tendsto_log_atTop.const_div_atTop (Real.log b)
  have h0 : Tendsto (fun r : ℝ => Real.log b / Real.log r - 1) atTop (𝓝 (-1)) := by
    simpa only [zero_sub] using hz.sub_const (1 : ℝ)
  have hl : Tendsto (fun r : ℝ => Real.log (b/r)/Real.log r) atTop (𝓝 (-1)) := by
    apply h0.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr
    rw [Real.log_div hb.ne' (by linarith : r ≠ 0)]
    have hlog : Real.log r ≠ 0 := (Real.log_pos hr).ne'
    field_simp
  have h := (hf.comp ht).mul hl
  simp only [mul_neg_one] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop b] with r hr
  have hp : 0 < b/r := div_pos hb (hb.trans hr)
  have hlt : b/r < 1 := (div_lt_one (hb.trans hr)).mpr hr
  have hlog : Real.log (b/r) ≠ 0 := (Real.log_neg hp hlt).ne
  dsimp only [Function.comp_apply]
  field_simp

theorem actualCentralCovarianceMinimumCDF_highSNR_diversity (d n : ℕ)
    (v : ℝ) (hv : 0 < v) (b : ℝ) (hb : 0 < b) :
    Tendsto (fun r : ℝ =>
      Real.log (actualCentralCovarianceMinimumCDF d n v (b/r))/Real.log r)
      atTop (𝓝 (-((d+1 : ℕ) : ℝ))) :=
  tendsto_log_ratio_inverse_threshold _ _
    (actualCentralCovarianceMinimumCDF_diversity d n v hv) b hb

end
end JinWishart
#print axioms JinWishart.actualCentralCovarianceMinimumCDF_eq
#print axioms JinWishart.actualCentralCovarianceMinimumCDF_local_bounds
#print axioms JinWishart.actualCentralCovarianceMinimumCDF_diversity
#print axioms JinWishart.tendsto_log_ratio_inverse_threshold
#print axioms JinWishart.actualCentralCovarianceMinimumCDF_highSNR_diversity
