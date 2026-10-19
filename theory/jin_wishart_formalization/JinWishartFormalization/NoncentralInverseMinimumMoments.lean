import JinWishartFormalization.NoncentralInverseMinimumFirstMoment
import JinWishartFormalization.ProbabilityTailNaturalMoments
import JinWishartFormalization.NoncentralMinimumCovarianceDiversity

/-!
# Exact nonnegative integer inverse-minimum moment threshold

Codex. Includes moment0 and critical exponent divergence. Fixed arbitrary mean
and fixed scalar covariance; no exact numerical moment value is claimed.
[需人工审查] Weighted layercake, model/variance and expectation interpretation.
-/
open Matrix MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

theorem actualNoncentralInverseMinimum_natMoment_integrable_iff (d n q : ℕ)
    (M : Matrix (Fin (d+(n+1))) (Fin (n+1)) ℂ) :
    Integrable (fun z => (actualNoncentralInverseMinimum d n M z)^q)
      (stdGaussian (ComplexSample (m := d+(n+1)) (n := n+1))) ↔ q<d+1 := by
  apply integrable_natPower_iff_two_sided_power_tail
    (stdGaussian (ComplexSample (m := d+(n+1)) (n := n+1)))
    (actualNoncentralInverseMinimum d n M) (measurable_actualNoncentralInverseMinimum d n M)
    (ae_of_all _ (actualNoncentralInverseMinimum_nonneg d n M)) q (d+1) (Nat.succ_pos d)
    (noncentralMinimumPowerLower d n M) (noncentralMinimumPowerUpper d n M)
    (noncentralMinimumPower_constants_pos d n M).1 (noncentralMinimumPower_constants_pos d n M).2
  intro t ht
  exact actualNoncentralInverseMinimumTail_power_bounds d n M t ht

theorem actualNoncentralRectangular_inverseMinimum_natMoment_integrable_iff (m n q : ℕ)
    (hn : 0<n) (hnm : n≤m) (M : Matrix (Fin m) (Fin n) ℂ) :
    Integrable (fun z : ComplexSample (m := m) (n := n) =>
      ((complexNoncentralSampleSmallestEigenvalue M hn z)⁻¹)^q) (stdGaussian _) ↔ q<m-n+1 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hm : m-(k+1)+(k+1)=m := Nat.sub_add_cancel hnm
  generalize hd : m-(k+1)=d at *
  subst m
  exact actualNoncentralInverseMinimum_natMoment_integrable_iff d k q M

theorem actualNoncentralInverseMinimum_natMoment_lintegral_eq_top (d n q : ℕ)
    (M : Matrix (Fin (d+(n+1))) (Fin (n+1)) ℂ) (hq : d+1≤q) :
    (∫⁻ z, ENNReal.ofReal ((actualNoncentralInverseMinimum d n M z)^q)
      ∂stdGaussian (ComplexSample (m := d+(n+1)) (n := n+1))) = ⊤ := by
  by_contra h
  have hi := (lintegral_ofReal_ne_top_iff_integrable
    ((measurable_actualNoncentralInverseMinimum d n M).pow_const q).aestronglyMeasurable
    (ae_of_all _ (fun z => pow_nonneg (actualNoncentralInverseMinimum_nonneg d n M z) q))).mp h
  exact (Nat.not_lt_of_ge hq) ((actualNoncentralInverseMinimum_natMoment_integrable_iff d n q M).mp hi)

theorem actualNoncentralCovariance_inverseMinimum_natMoment_integrable_iff (d n q : ℕ)
    (M : Matrix (Fin (d+(n+1))) (Fin (n+1)) ℂ) (v : ℝ) (hv : 0<v) :
    Integrable (fun z : ComplexSample (m := d+(n+1)) (n := n+1) =>
      ((complexNoncentralSampleSmallestEigenvalue M (Nat.succ_pos n) (Real.sqrt v • z))⁻¹)^q)
      (stdGaussian _) ↔ q<d+1 := by
  let M' : Matrix (Fin (d+(n+1))) (Fin (n+1)) ℂ := (((Real.sqrt v)⁻¹ : ℝ) : ℂ) • M
  have he : (fun z : ComplexSample (m := d+(n+1)) (n := n+1) =>
      ((complexNoncentralSampleSmallestEigenvalue M (Nat.succ_pos n) (Real.sqrt v • z))⁻¹)^q) =
      (fun z => (v⁻¹)^q*(actualNoncentralInverseMinimum d n M' z)^q) := by
    funext z
    rw [noncentralSampleMinimum_amplitude_scale _ _ _ (Real.sqrt_pos.mpr hv),
      Real.sq_sqrt hv.le,_root_.mul_inv_rev,mul_pow]
    simp only [actualNoncentralInverseMinimum,M',mul_comm]
  rw [he,integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (pow_ne_zero q (inv_ne_zero hv.ne')))]
  exact actualNoncentralInverseMinimum_natMoment_integrable_iff d n q M'

end
end JinWishart
#print axioms JinWishart.actualNoncentralInverseMinimum_natMoment_integrable_iff
#print axioms JinWishart.actualNoncentralRectangular_inverseMinimum_natMoment_integrable_iff
#print axioms JinWishart.actualNoncentralInverseMinimum_natMoment_lintegral_eq_top
#print axioms JinWishart.actualNoncentralCovariance_inverseMinimum_natMoment_integrable_iff
