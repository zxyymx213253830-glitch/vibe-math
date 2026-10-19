import JinWishartFormalization.NoncentralMinimumDiversity

/-!
# Fixed arbitrary noncentral mean with positive scalar covariance

Codex proofs. Noise is sqrt(v)Z while the mean M remains FIXED, not scaled.
[需人工审查] Complex scalar/real-source encoding, variance and outage model.
-/
open Matrix Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace JinWishart
noncomputable section

theorem complexSampleMean_real_smul {m n : ℕ} (a : ℝ) (M : Matrix (Fin m) (Fin n) ℂ) :
    complexSampleMean ((a : ℂ) • M) = a • complexSampleMean M := by
  ext ij
  by_cases h : ij.2=0
  · simp [complexSampleMean,PiLp.smul_apply,Matrix.smul_apply,smul_eq_mul,h]
    ring
  · simp [complexSampleMean,PiLp.smul_apply,Matrix.smul_apply,smul_eq_mul,h]
    ring

theorem noncentralSampleMinimum_amplitude_scale {m n : ℕ} (hn : 0 < n)
    (M : Matrix (Fin m) (Fin n) ℂ) (a : ℝ) (ha : 0 < a)
    (z : ComplexSample (m := m) (n := n)) :
    complexNoncentralSampleSmallestEigenvalue M hn (a • z) =
      a^2*complexNoncentralSampleSmallestEigenvalue (((a⁻¹ : ℝ) : ℂ) • M) hn z := by
  let M' : Matrix (Fin m) (Fin n) ℂ := ((a⁻¹ : ℝ) : ℂ) • M
  have hmean : a • complexSampleMean M' = complexSampleMean M := by
    dsimp only [M']
    rw [complexSampleMean_real_smul,smul_smul,mul_inv_cancel₀ ha.ne',one_smul]
  have he : a • (z+complexSampleMean M') = a • z+complexSampleMean M := by
    rw [smul_add,hmean]
  rw [← centralGaussianSampleMinimum_shift M hn,← he,
    centralGaussianSampleMinimum_scale m n hn a ha,centralGaussianSampleMinimum_shift]

def actualNoncentralCovarianceMinimumCDF (d n : ℕ)
    (M : Matrix (Fin (d+(n+1))) (Fin (n+1)) ℂ) (v x : ℝ) : ℝ :=
  (stdGaussian (ComplexSample (m := d+(n+1)) (n := n+1))).real
    {z | complexNoncentralSampleSmallestEigenvalue M (Nat.succ_pos n) (Real.sqrt v • z) ≤ x}

theorem actualNoncentralCovarianceMinimumCDF_eq (d n : ℕ)
    (M : Matrix (Fin (d+(n+1))) (Fin (n+1)) ℂ) (v : ℝ) (hv : 0 < v) (x : ℝ) :
    actualNoncentralCovarianceMinimumCDF d n M v x =
      actualNoncentralMinimumCDF d n ((((Real.sqrt v)⁻¹ : ℝ) : ℂ) • M) (x/v) := by
  unfold actualNoncentralCovarianceMinimumCDF actualNoncentralMinimumCDF
  congr 1
  ext z
  simp only [Set.mem_setOf_eq,noncentralSampleMinimum_amplitude_scale _ _ _ (Real.sqrt_pos.mpr hv),
    Real.sq_sqrt hv.le]
  rw [le_div_iff₀ hv,mul_comm]

theorem tendsto_log_ratio_div_const (f : ℝ → ℝ) (a : ℝ)
    (hf : Tendsto (fun x => Real.log (f x)/Real.log x) (𝓝[>] 0) (𝓝 a))
    (v : ℝ) (hv : 0 < v) :
    Tendsto (fun x : ℝ => Real.log (f (x/v))/Real.log x) (𝓝[>] 0) (𝓝 a) := by
  have ht : Tendsto (fun x : ℝ => x/v) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [zero_div,id_eq] using
        ((tendsto_id : Tendsto (fun x : ℝ => x) (𝓝 0) (𝓝 0)).div_const v).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact div_pos hx hv
  have hz := Real.tendsto_log_nhdsGT_zero.const_div_atBot (Real.log v)
  have h0 : Tendsto (fun x : ℝ => 1-Real.log v / Real.log x) (𝓝[>] 0) (𝓝 1) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] 0) (𝓝 1)).sub hz
  have hl : Tendsto (fun x : ℝ => Real.log (x/v)/Real.log x) (𝓝[>] 0) (𝓝 1) := by
    apply h0.congr'
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ)<1)).filter_mono nhdsWithin_le_nhds] with x hx hx1
    rw [Real.log_div hx.ne' hv.ne']
    have hx0 : Real.log x ≠ 0 := (Real.log_neg hx hx1).ne
    field_simp
  have h := (hf.comp ht).mul hl
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hv).filter_mono nhdsWithin_le_nhds] with x hx hxv
  have hlog : Real.log (x/v) ≠ 0 := (Real.log_neg (div_pos hx hv) ((div_lt_one hv).mpr hxv)).ne
  dsimp only [Function.comp_apply]
  field_simp

theorem actualNoncentralCovarianceMinimumCDF_diversity (d n : ℕ)
    (M : Matrix (Fin (d+(n+1))) (Fin (n+1)) ℂ) (v : ℝ) (hv : 0 < v) :
    Tendsto (fun x : ℝ => Real.log (actualNoncentralCovarianceMinimumCDF d n M v x)/Real.log x)
      (𝓝[>] 0) (𝓝 ((d+1 : ℕ) : ℝ)) := by
  have h := tendsto_log_ratio_div_const _ _
    (actualNoncentralMinimumCDF_diversity d n ((((Real.sqrt v)⁻¹ : ℝ) : ℂ) • M)) v hv
  simpa only [actualNoncentralCovarianceMinimumCDF_eq d n M v hv] using h

theorem actualNoncentralCovarianceMinimumCDF_highSNR_diversity (d n : ℕ)
    (M : Matrix (Fin (d+(n+1))) (Fin (n+1)) ℂ) (v : ℝ) (hv : 0 < v) (b : ℝ) (hb : 0 < b) :
    Tendsto (fun r : ℝ => Real.log (actualNoncentralCovarianceMinimumCDF d n M v (b/r))/Real.log r)
      atTop (𝓝 (-((d+1 : ℕ) : ℝ))) :=
  tendsto_log_ratio_inverse_threshold _ _ (actualNoncentralCovarianceMinimumCDF_diversity d n M v hv) b hb

end
end JinWishart
#print axioms JinWishart.complexSampleMean_real_smul
#print axioms JinWishart.noncentralSampleMinimum_amplitude_scale
#print axioms JinWishart.actualNoncentralCovarianceMinimumCDF_eq
#print axioms JinWishart.tendsto_log_ratio_div_const
#print axioms JinWishart.actualNoncentralCovarianceMinimumCDF_diversity
#print axioms JinWishart.actualNoncentralCovarianceMinimumCDF_highSNR_diversity
