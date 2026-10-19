import JinWishartFormalization.NoncentralMinimumComparison

/-!
# Arbitrary fixed-mean noncentral complex Wishart minimum diversity

Codex proofs. Neither a noncentral spectral density nor a sharp T4 constant
is assumed. Constants depend on the fixed deterministic mean.
[需人工审查] Mean/variance encoding, minimum spectral event and log exponent.
-/
open Matrix Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace JinWishart
noncomputable section

def noncentralMinimumPowerLower (d n : ℕ)
    (M : Matrix (Fin (d+(n+1))) (Fin (n+1)) ℂ) : ℝ :=
  gaussianShiftLowerConstant (complexSampleMean M) *
    (Real.exp (-1)/(Nat.factorial (d+1) : ℝ)/(1/4 : ℝ)^(d+1))

def noncentralMinimumPowerUpper (d n : ℕ)
    (M : Matrix (Fin (d+(n+1))) (Fin (n+1)) ℂ) : ℝ :=
  gaussianShiftUpperConstant (complexSampleMean M) *
    (((n+1 : ℕ) : ℝ)^(d+2)/(Nat.factorial (d+1) : ℝ)/(4 : ℝ)^(d+1))

theorem noncentralMinimumPower_constants_pos (d n : ℕ)
    (M : Matrix (Fin (d+(n+1))) (Fin (n+1)) ℂ) :
    0 < noncentralMinimumPowerLower d n M ∧ 0 < noncentralMinimumPowerUpper d n M := by
  unfold noncentralMinimumPowerLower noncentralMinimumPowerUpper
    gaussianShiftLowerConstant gaussianShiftUpperConstant
  constructor <;> positivity

theorem actualNoncentralMinimumCDF_local_power_bounds (d n : ℕ)
    (M : Matrix (Fin (d+(n+1))) (Fin (n+1)) ℂ) (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1/4) :
    noncentralMinimumPowerLower d n M*x^(d+1) ≤ actualNoncentralMinimumCDF d n M x ∧
    actualNoncentralMinimumCDF d n M x ≤ noncentralMinimumPowerUpper d n M*x^(d+1) := by
  have hs := actualNoncentralMinimumCDF_central_comparison d n M x
  have hlo := actualCentralCovarianceMinimumCDF_local_bounds d n (1/4) (by norm_num) x hx hx1
  have hup := actualCentralCovarianceMinimumCDF_local_bounds d n 4 (by norm_num) x hx (by linarith)
  have hc : 0 ≤ gaussianShiftLowerConstant (complexSampleMean M) := by
    unfold gaussianShiftLowerConstant; positivity
  have hC : 0 ≤ gaussianShiftUpperConstant (complexSampleMean M) := by
    unfold gaussianShiftUpperConstant; positivity
  constructor
  · simpa only [noncentralMinimumPowerLower,mul_assoc] using
      (mul_le_mul_of_nonneg_left hlo.1 hc).trans hs.1
  · simpa only [noncentralMinimumPowerUpper,mul_assoc] using
      hs.2.trans (mul_le_mul_of_nonneg_left hup.2 hC)

theorem actualNoncentralMinimumCDF_diversity (d n : ℕ)
    (M : Matrix (Fin (d+(n+1))) (Fin (n+1)) ℂ) :
    Tendsto (fun x : ℝ => Real.log (actualNoncentralMinimumCDF d n M x)/Real.log x)
      (𝓝[>] 0) (𝓝 ((d+1 : ℕ) : ℝ)) := by
  apply tendsto_log_ratio_of_power_bounds _ (d+1)
    (noncentralMinimumPowerLower d n M) (noncentralMinimumPowerUpper d n M)
    (noncentralMinimumPower_constants_pos d n M).1 (noncentralMinimumPower_constants_pos d n M).2
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0 : ℝ)<1/4)).filter_mono nhdsWithin_le_nhds] with x hx hx1
  exact ⟨hx,actualNoncentralMinimumCDF_local_power_bounds d n M x hx hx1.le⟩

theorem actualNoncentralRectangular_minimum_diversity (m n : ℕ) (hn : 0 < n) (hnm : n ≤ m)
    (M : Matrix (Fin m) (Fin n) ℂ) :
    Tendsto (fun x : ℝ => Real.log ((stdGaussian (ComplexSample (m := m) (n := n))).real
      {z | complexNoncentralSampleSmallestEigenvalue M hn z ≤ x})/Real.log x)
      (𝓝[>] 0) (𝓝 ((m-n+1 : ℕ) : ℝ)) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hm : m-(k+1)+(k+1)=m := Nat.sub_add_cancel hnm
  generalize hd : m-(k+1)=d at *
  subst m
  exact actualNoncentralMinimumCDF_diversity d k M

theorem actualNoncentralMinimumCDF_highSNR_diversity (d n : ℕ)
    (M : Matrix (Fin (d+(n+1))) (Fin (n+1)) ℂ) (b : ℝ) (hb : 0 < b) :
    Tendsto (fun r : ℝ => Real.log (actualNoncentralMinimumCDF d n M (b/r))/Real.log r)
      atTop (𝓝 (-((d+1 : ℕ) : ℝ))) :=
  tendsto_log_ratio_inverse_threshold _ _ (actualNoncentralMinimumCDF_diversity d n M) b hb

end
end JinWishart
#print axioms JinWishart.noncentralMinimumPower_constants_pos
#print axioms JinWishart.actualNoncentralMinimumCDF_local_power_bounds
#print axioms JinWishart.actualNoncentralMinimumCDF_diversity
#print axioms JinWishart.actualNoncentralRectangular_minimum_diversity
#print axioms JinWishart.actualNoncentralMinimumCDF_highSNR_diversity
