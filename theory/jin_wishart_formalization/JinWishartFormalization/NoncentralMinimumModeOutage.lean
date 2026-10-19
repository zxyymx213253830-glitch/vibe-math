import JinWishartFormalization.NoncentralMinimumCovarianceDiversity

/-!
# A worst-mode outage application (a monotone-transform corollary)

This is log(1+rho*lambda_min), NOT full MIMO log-det mutual information.
Rate R is measured in natural-log units. Codex proofs.
[需人工审查] Communication model and outage-event interpretation.
-/
open Matrix Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace JinWishart
noncomputable section

theorem minimum_mode_log_threshold (l : ℝ) (hl : 0 ≤ l) (r : ℝ) (hr : 0 < r) (R : ℝ) :
    Real.log (1+r*l) ≤ R ↔ l ≤ (Real.exp R-1)/r := by
  rw [Real.log_le_iff_le_exp (by positivity),le_div_iff₀ hr]
  constructor <;> intro h <;> nlinarith

def actualNoncentralMinimumModeOutage (d n : ℕ)
    (M : Matrix (Fin (d+(n+1))) (Fin (n+1)) ℂ) (v R r : ℝ) : ℝ :=
  (stdGaussian (ComplexSample (m := d+(n+1)) (n := n+1))).real
    {z | Real.log (1+r*complexNoncentralSampleSmallestEigenvalue M (Nat.succ_pos n)
      (Real.sqrt v • z)) ≤ R}

theorem actualNoncentralMinimumModeOutage_eq_CDF (d n : ℕ)
    (M : Matrix (Fin (d+(n+1))) (Fin (n+1)) ℂ) (v R r : ℝ) (hr : 0 < r) :
    actualNoncentralMinimumModeOutage d n M v R r =
      actualNoncentralCovarianceMinimumCDF d n M v ((Real.exp R-1)/r) := by
  unfold actualNoncentralMinimumModeOutage actualNoncentralCovarianceMinimumCDF
  congr 1
  ext z
  exact minimum_mode_log_threshold _ (complexNoncentralGram_eigenvalues₀_nonneg _ _ _) r hr R

theorem actualNoncentralMinimumModeOutage_diversity (d n : ℕ)
    (M : Matrix (Fin (d+(n+1))) (Fin (n+1)) ℂ) (v : ℝ) (hv : 0 < v)
    (R : ℝ) (hR : 0 < R) :
    Tendsto (fun r : ℝ => Real.log (actualNoncentralMinimumModeOutage d n M v R r)/Real.log r)
      atTop (𝓝 (-((d+1 : ℕ) : ℝ))) := by
  have hb : 0 < Real.exp R-1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hR)
  apply (actualNoncentralCovarianceMinimumCDF_highSNR_diversity d n M v hv (Real.exp R-1) hb).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  rw [actualNoncentralMinimumModeOutage_eq_CDF d n M v R r hr]

end
end JinWishart
#print axioms JinWishart.minimum_mode_log_threshold
#print axioms JinWishart.actualNoncentralMinimumModeOutage_eq_CDF
#print axioms JinWishart.actualNoncentralMinimumModeOutage_diversity
