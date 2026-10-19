import JinWishartFormalization.ActualLogDetError
import JinWishartFormalization.LogErrorDivergence

/-! Square actual fixed-mean Gram samples have divergent rho-scaled logdet error.
Codex. The finite real error tends to zero, while rho times it tends to +infinity.
[需人工审查] Fatou, inverse-moment boundary and actual-model interpretation.
-/
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace JinWishart
noncomputable section

theorem actualSquare_scaled_minimum_log_error_atTop {n : ℕ} (hn : 0 < n)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    Tendsto (fun r : ℝ => r*(∫ z, Real.log
      (1+(r*complexNoncentralSampleSmallestEigenvalue M hn z)⁻¹) ∂stdGaussian _)) atTop atTop := by
  have hpos := actualNoncentral_minimum_pos_ae hn le_rfl M
  have hf : AEMeasurable (complexNoncentralSampleSmallestEigenvalue M hn) (stdGaussian _) :=
    (measurable_complexNoncentralSampleSmallestEigenvalue M hn).aemeasurable
  have hi := (actualNoncentralRectangular_inverseMinimum_realMoment_integrable_iff
    n n hn le_rfl M (1/2) (by norm_num)).mpr (by norm_num)
  have htop : (∫⁻ z, ENNReal.ofReal ((complexNoncentralSampleSmallestEigenvalue M hn z)⁻¹)
      ∂stdGaussian _) = ⊤ := by
    by_contra h
    have hinv := (lintegral_ofReal_ne_top_iff_integrable hf.inv.aestronglyMeasurable
      (ae_of_all _ (fun z => inv_nonneg.mpr (complexNoncentralGram_eigenvalues₀_nonneg M z _)))).mp h
    exact (Nat.lt_irrefl n)
      ((actualNoncentralRectangular_inverseMinimum_integrable_iff n n hn le_rfl M).mp hinv)
  exact scaled_log_inverse_error_tendsto_atTop _ _ hf hpos (1/2)
    (by norm_num) (by norm_num) hi htop

theorem actualLogDetOffsetError_minimum_lower_bound {m n : ℕ} (hn : 0 < n) (hnm : n ≤ m)
    (M : Matrix (Fin m) (Fin n) ℂ) (r : ℝ) (hr : 0 < r) :
    (∫ z, Real.log (1+(r*complexNoncentralSampleSmallestEigenvalue M hn z)⁻¹) ∂stdGaussian _) ≤
      actualNoncentralLogDetOffsetError M r := by
  classical
  have hpk : (1/2 : ℝ) < ((m-n+1 : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((m-n+1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ m-n+1 by omega)
    linarith
  have hpos := actualNoncentral_minimum_pos_ae hn hnm M
  have hi := integrable_log_inverse_error (stdGaussian _) _
    (measurable_complexNoncentralSampleSmallestEigenvalue M hn).aemeasurable hpos
    r (1/2) hr (by norm_num) (by norm_num)
      ((actualNoncentralRectangular_inverseMinimum_realMoment_integrable_iff
        m n hn hnm M (1/2) (by norm_num)).mpr hpk)
  have his (i : Fin (Fintype.card (Fin n))) := integrable_log_inverse_error (stdGaussian _)
    (complexNoncentralSampleEigenvalue M i) (measurable_actualNoncentralEigenvalue M i).aemeasurable
    (hpos.mono (fun z hz => hz.trans_le (actualNoncentralMinimum_le_eigenvalue hn M i z)))
    r (1/2) hr (by norm_num) (by norm_num)
      (integrable_actualNoncentral_inverseEigenvalue_rpow hn hnm M i (1/2) (by norm_num) hpk)
  rw [actualNoncentralLogDetOffsetError_eq hn hnm M r hr]
  apply integral_mono_ae hi (integrable_finsetSum Finset.univ (fun i _ => his i))
  exact ae_of_all _ (fun z => by
    change Real.log (1+(r*complexNoncentralSampleEigenvalue M (smallestEigenvalue₀Index hn) z)⁻¹) ≤
      ∑ i, Real.log (1+(r*complexNoncentralSampleEigenvalue M i z)⁻¹)
    exact Finset.single_le_sum
      (fun i _ => Real.log_nonneg (by
        change 1 ≤ 1+(r*complexNoncentralSampleEigenvalue M i z)⁻¹
        have : 0 ≤ (r*complexNoncentralSampleEigenvalue M i z)⁻¹ :=
          inv_nonneg.mpr (mul_nonneg hr.le (complexNoncentralSampleEigenvalue_nonneg M i z))
        linarith)) (Finset.mem_univ (smallestEigenvalue₀Index hn)))

theorem actualSquareLogDetOffsetError_scaled_atTop {n : ℕ} (hn : 0 < n)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    Tendsto (fun r : ℝ => r*actualNoncentralLogDetOffsetError M r) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ (actualSquare_scaled_minimum_log_error_atTop hn M)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  exact mul_le_mul_of_nonneg_left (actualLogDetOffsetError_minimum_lower_bound hn le_rfl M r hr) hr.le

end
end JinWishart
#print axioms JinWishart.actualSquare_scaled_minimum_log_error_atTop
#print axioms JinWishart.actualLogDetOffsetError_minimum_lower_bound
#print axioms JinWishart.actualSquareLogDetOffsetError_scaled_atTop
