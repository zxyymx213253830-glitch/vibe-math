import JinWishartFormalization.ActualGramLogDet
import JinWishartFormalization.LogDetErrorBounds
import JinWishartFormalization.LogDetOffsetIdentity

/-! Quantitative actual fixed-mean full log-det offset error.
Codex. No joint density. [需人工审查] Expectation and variance/model interpretation.
-/
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace JinWishart
noncomputable section

def actualNoncentralLogDetOffsetError {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) (r : ℝ) : ℝ :=
  (∫ z, actualNoncentralMatrixLogDet M r z ∂stdGaussian _)-(n : ℝ)*Real.log r-
    (∫ z, Real.log (complexGram (complexSampleMatrix z+M)).det.re ∂stdGaussian _)

theorem integrable_actualNoncentral_inverseEigenvalue_rpow {m n : ℕ}
    (hn : 0 < n) (hnm : n ≤ m) (M : Matrix (Fin m) (Fin n) ℂ)
    (i : Fin (Fintype.card (Fin n))) (p : ℝ) (hp : 0 < p)
    (hpk : p < ((m-n+1 : ℕ) : ℝ)) :
    Integrable (fun z => (complexNoncentralSampleEigenvalue M i z)⁻¹ ^ p) (stdGaussian _) := by
  have hmin := (actualNoncentralRectangular_inverseMinimum_realMoment_integrable_iff
    m n hn hnm M p hp).mpr hpk
  apply hmin.mono'
    (((measurable_actualNoncentralEigenvalue M i).inv).pow_const p).aestronglyMeasurable
  filter_upwards [actualNoncentral_minimum_pos_ae hn hnm M] with z hz
  have hnonneg := inv_nonneg.mpr (complexNoncentralSampleEigenvalue_nonneg M i z)
  change ‖(complexNoncentralSampleEigenvalue M i z)⁻¹ ^ p‖ ≤
    (complexNoncentralSampleSmallestEigenvalue M hn z)⁻¹ ^ p
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hnonneg _)]
  exact Real.rpow_le_rpow hnonneg (inv_anti₀ hz (actualNoncentralMinimum_le_eigenvalue hn M i z)) hp.le

theorem actualNoncentralLogDetOffsetError_eq {m n : ℕ} (hn : 0 < n) (hnm : n ≤ m)
    (M : Matrix (Fin m) (Fin n) ℂ) (r : ℝ) (hr : 0 < r) :
    actualNoncentralLogDetOffsetError M r =
      ∫ z, ∑ i, Real.log (1+(r*complexNoncentralSampleEigenvalue M i z)⁻¹) ∂stdGaussian _ := by
  unfold actualNoncentralLogDetOffsetError
  have hi := integrable_actualNoncentralMatrixLogDet M r hr.le
  have hlog := integrable_actualNoncentral_logGramDet hn hnm M
  calc
    _ = ∫ z, (actualNoncentralMatrixLogDet M r z-(n : ℝ)*Real.log r-
        Real.log (complexGram (complexSampleMatrix z+M)).det.re) ∂stdGaussian _ := by
      have he := integral_sub (hi.sub (integrable_const ((n : ℝ)*Real.log r))) hlog
      have hc := integral_sub hi (integrable_const ((n : ℝ)*Real.log r))
      simp only [Pi.sub_apply] at he hc
      rw [he,hc]
      simp
    _ = _ := integral_congr_ae (by
      filter_upwards [actualNoncentral_minimum_pos_ae hn hnm M,
        actualNoncentral_logGramDet_eq_sum_log_ae hn hnm M] with z hz he
      change actualNoncentralMatrixLogDet M r z-(n : ℝ)*Real.log r-
        Real.log (complexGram (complexSampleMatrix z+M)).det.re = _
      rw [← actualNoncentralGramLogDet_eq_matrix M r hr.le z,he]
      simpa only [actualNoncentralGramLogDet,Fintype.card_fin] using
        finiteSpectrumLogDet_offset_error (fun i => complexNoncentralSampleEigenvalue M i z)
          (fun i => hz.trans_le (actualNoncentralMinimum_le_eigenvalue hn M i z)) r hr)

theorem actualNoncentralLogDetOffsetError_bounds {m n : ℕ} (hn : 0 < n) (hnm : n ≤ m)
    (M : Matrix (Fin m) (Fin n) ℂ) (r p : ℝ) (hr : 0 < r) (hp : 0 < p)
    (hp1 : p ≤ 1) (hpk : p < ((m-n+1 : ℕ) : ℝ)) :
    0 ≤ actualNoncentralLogDetOffsetError M r ∧
      actualNoncentralLogDetOffsetError M r ≤ (r^p)⁻¹/p*
        ∑ i, ∫ z, (complexNoncentralSampleEigenvalue M i z)⁻¹ ^ p ∂stdGaussian _ := by
  classical
  have hpos (i : Fin (Fintype.card (Fin n))) :=
    (actualNoncentral_minimum_pos_ae hn hnm M).mono (fun z hz =>
      hz.trans_le (actualNoncentralMinimum_le_eigenvalue hn M i z))
  have hinv (i : Fin (Fintype.card (Fin n))) :=
    integrable_actualNoncentral_inverseEigenvalue_rpow hn hnm M i p hp hpk
  have hi (i : Fin (Fintype.card (Fin n))) := integrable_log_inverse_error (stdGaussian _)
    (complexNoncentralSampleEigenvalue M i) (measurable_actualNoncentralEigenvalue M i).aemeasurable
    (hpos i) r p hr hp hp1 (hinv i)
  have hb (i : Fin (Fintype.card (Fin n))) := integral_log_inverse_error_bounds (stdGaussian _)
    (complexNoncentralSampleEigenvalue M i) (measurable_actualNoncentralEigenvalue M i).aemeasurable
    (hpos i) r p hr hp hp1 (hinv i)
  rw [actualNoncentralLogDetOffsetError_eq hn hnm M r hr,
    integral_finsetSum _ (fun i _ => hi i)]
  constructor
  · exact Finset.sum_nonneg (fun i _ => (hb i).1)
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => (hb i).2)

theorem actualNoncentralLogDetOffsetError_first_order {m n : ℕ} (hn : 0 < n) (hnm : n < m)
    (M : Matrix (Fin m) (Fin n) ℂ) :
    Tendsto (fun r : ℝ => r*actualNoncentralLogDetOffsetError M r) atTop
      (𝓝 (∑ i, ∫ z, (complexNoncentralSampleEigenvalue M i z)⁻¹ ∂stdGaussian _)) := by
  classical
  have hpos (i : Fin (Fintype.card (Fin n))) :=
    (actualNoncentral_minimum_pos_ae hn hnm.le M).mono (fun z hz =>
      hz.trans_le (actualNoncentralMinimum_le_eigenvalue hn M i z))
  have hinv (i : Fin (Fintype.card (Fin n))) :
      Integrable (fun z => (complexNoncentralSampleEigenvalue M i z)⁻¹) (stdGaussian _) := by
    have hpk : (1 : ℝ) < ((m-n+1 : ℕ) : ℝ) := by exact_mod_cast (show 1 < m-n+1 by omega)
    simpa only [Real.rpow_one] using
      integrable_actualNoncentral_inverseEigenvalue_rpow hn hnm.le M i 1 (by norm_num) hpk
  have ht := tendsto_finsetSum Finset.univ (fun i _ => integral_log_inverse_error_first_order
    (stdGaussian _) (complexNoncentralSampleEigenvalue M i)
      (measurable_actualNoncentralEigenvalue M i).aemeasurable (hpos i) (hinv i))
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have hi (i : Fin (Fintype.card (Fin n))) : Integrable
      (fun z => Real.log (1+(r*complexNoncentralSampleEigenvalue M i z)⁻¹)) (stdGaussian _) := by
    apply integrable_log_inverse_error (stdGaussian _) _
      (measurable_actualNoncentralEigenvalue M i).aemeasurable (hpos i) r 1 hr (by norm_num) (by norm_num)
    simpa only [Real.rpow_one] using hinv i
  rw [actualNoncentralLogDetOffsetError_eq hn hnm.le M r hr,
    integral_finsetSum _ (fun i _ => hi i),Finset.mul_sum]

end
end JinWishart
#print axioms JinWishart.integrable_actualNoncentral_inverseEigenvalue_rpow
#print axioms JinWishart.actualNoncentralLogDetOffsetError_eq
#print axioms JinWishart.actualNoncentralLogDetOffsetError_bounds
#print axioms JinWishart.actualNoncentralLogDetOffsetError_first_order
