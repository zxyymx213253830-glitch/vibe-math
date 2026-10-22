import JinWishartFormalization.ProperGaussianAdjointLaw
import JinWishartFormalization.NoncentralInverseMinimumRealMoments
import JinWishartFormalization.CorrelatedColumnMinimum

/-! Wide fixed-mean IID model: inverse moments of the least ROW-Gram eigenvalue.
This is gramSmallestValue X^H, not the structurally zero least column-Gram
value when n>m. Codex. [需人工审查] Pushforward/integrability and model meaning.
No general singular covariance-factor theorem. -/
open Matrix MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

private theorem tallLaw (m n : ℕ) (hn : 0<n) (hnm : n≤m)
    (M : Matrix (Fin m) (Fin n) ℂ) (p : ℝ) (hp : 0<p) :
    Integrable (fun X => ((gramSmallestValue X hn)⁻¹)^p) (complexGaussianMatrixLaw M) ↔
      p<((m-n+1 : ℕ) : ℝ) := by
  have hF : Measurable (fun X : Matrix (Fin m) (Fin n) ℂ => ((gramSmallestValue X hn)⁻¹)^p) :=
    (measurable_gramSmallestValue hn).inv.pow_const p
  unfold complexGaussianMatrixLaw
  rw [integrable_map_measure hF.aestronglyMeasurable
    (measurable_shiftedComplexSampleMatrix M).aemeasurable]
  simpa only [Function.comp_def, gramSmallestValue, complexNoncentralSampleSmallestEigenvalue] using
    actualNoncentralRectangular_inverseMinimum_realMoment_integrable_iff m n hn hnm M p hp

theorem wideRowMinimum_inverse_realMoment_integrable_iff (m n : ℕ)
    (hm : 0<m) (hmn : m≤n) (M : Matrix (Fin m) (Fin n) ℂ) (p : ℝ) (hp : 0<p) :
    Integrable (fun X => ((gramSmallestValue Xᴴ hm)⁻¹)^p) (complexGaussianMatrixLaw M) ↔
      p<((n-m+1 : ℕ) : ℝ) := by
  have hF : Measurable (fun Y : Matrix (Fin n) (Fin m) ℂ => ((gramSmallestValue Y hm)⁻¹)^p) :=
    (measurable_gramSmallestValue hm).inv.pow_const p
  have h := tallLaw n m hm hmn Mᴴ p hp
  rw [← complexGaussianMatrixLaw_conjTranspose M,
    integrable_map_measure hF.aestronglyMeasurable (by fun_prop)] at h
  exact h

theorem wideRowMinimum_inverse_realMoment_lintegral_eq_top (m n : ℕ)
    (hm : 0<m) (hmn : m≤n) (M : Matrix (Fin m) (Fin n) ℂ)
    (p : ℝ) (hp : ((n-m+1 : ℕ) : ℝ)≤p) :
    (∫⁻ X, ENNReal.ofReal (((gramSmallestValue Xᴴ hm)⁻¹)^p)
      ∂complexGaussianMatrixLaw M) = ⊤ := by
  have hp0 : 0<p := lt_of_lt_of_le (by positivity : (0 : ℝ)<((n-m+1 : ℕ) : ℝ)) hp
  have hF : Measurable (fun X : Matrix (Fin m) (Fin n) ℂ => ((gramSmallestValue Xᴴ hm)⁻¹)^p) :=
    ((measurable_gramSmallestValue hm).comp (by fun_prop)).inv.pow_const p
  by_contra h
  have hi := (lintegral_ofReal_ne_top_iff_integrable hF.aestronglyMeasurable
    (ae_of_all _ (fun X => Real.rpow_nonneg (inv_nonneg.mpr (gramSmallestValue_nonneg Xᴴ hm)) p))).mp h
  exact (not_lt_of_ge hp) ((wideRowMinimum_inverse_realMoment_integrable_iff m n hm hmn M p hp0).mp hi)

end
end JinWishart
#print axioms JinWishart.wideRowMinimum_inverse_realMoment_integrable_iff
#print axioms JinWishart.wideRowMinimum_inverse_realMoment_lintegral_eq_top
