import JinWishartFormalization.NoncentralInverseMinimumFirstMoment
import JinWishartFormalization.ProbabilityTailRealMoments
import JinWishartFormalization.NoncentralMinimumCovarianceDiversity

/-!
# Sharp positive REAL inverse-minimum moment threshold

Codex. Includes fractional exponents and the critical divergence boundary.
Fixed arbitrary mean and fixed positive scalar covariance. No exact moment value.
[需人工审查] Real powers, weighted Fubini, model/variance and expectation meaning.
-/
open Matrix MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

theorem actualNoncentralInverseMinimum_realMoment_integrable_iff (d n : ℕ)
    (M : Matrix (Fin (d+(n+1))) (Fin (n+1)) ℂ) (p : ℝ) (hp : 0<p) :
    Integrable (fun z => (actualNoncentralInverseMinimum d n M z)^p)
      (stdGaussian (ComplexSample (m := d+(n+1)) (n := n+1))) ↔ p<((d+1 : ℕ) : ℝ) := by
  apply integrable_positiveRealPower_iff_two_sided_power_tail
    (stdGaussian (ComplexSample (m := d+(n+1)) (n := n+1)))
    (actualNoncentralInverseMinimum d n M) (measurable_actualNoncentralInverseMinimum d n M)
    (ae_of_all _ (actualNoncentralInverseMinimum_nonneg d n M)) p hp (d+1)
    (noncentralMinimumPowerLower d n M) (noncentralMinimumPowerUpper d n M)
    (noncentralMinimumPower_constants_pos d n M).1 (noncentralMinimumPower_constants_pos d n M).2
  intro t ht
  exact actualNoncentralInverseMinimumTail_power_bounds d n M t ht

theorem actualNoncentralRectangular_inverseMinimum_realMoment_integrable_iff (m n : ℕ)
    (hn : 0<n) (hnm : n≤m) (M : Matrix (Fin m) (Fin n) ℂ) (p : ℝ) (hp : 0<p) :
    Integrable (fun z : ComplexSample (m := m) (n := n) =>
      ((complexNoncentralSampleSmallestEigenvalue M hn z)⁻¹)^p) (stdGaussian _) ↔
        p<((m-n+1 : ℕ) : ℝ) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hm : m-(k+1)+(k+1)=m := Nat.sub_add_cancel hnm
  generalize hd : m-(k+1)=d at *
  subst m
  exact actualNoncentralInverseMinimum_realMoment_integrable_iff d k M p hp

theorem actualNoncentralInverseMinimum_realMoment_lintegral_eq_top (d n : ℕ)
    (M : Matrix (Fin (d+(n+1))) (Fin (n+1)) ℂ) (p : ℝ) (hp : ((d+1 : ℕ) : ℝ)≤p) :
    (∫⁻ z, ENNReal.ofReal ((actualNoncentralInverseMinimum d n M z)^p)
      ∂stdGaussian (ComplexSample (m := d+(n+1)) (n := n+1))) = ⊤ := by
  have hp0 : 0<p := lt_of_lt_of_le (by positivity : (0 : ℝ)<((d+1 : ℕ) : ℝ)) hp
  by_contra h
  have hi := (lintegral_ofReal_ne_top_iff_integrable
    ((measurable_actualNoncentralInverseMinimum d n M).pow_const p).aestronglyMeasurable
    (ae_of_all _ (fun z => Real.rpow_nonneg (actualNoncentralInverseMinimum_nonneg d n M z) p))).mp h
  exact (not_lt_of_ge hp) ((actualNoncentralInverseMinimum_realMoment_integrable_iff d n M p hp0).mp hi)

theorem actualNoncentralCovariance_inverseMinimum_realMoment_integrable_iff (d n : ℕ)
    (M : Matrix (Fin (d+(n+1))) (Fin (n+1)) ℂ) (p : ℝ) (hp : 0<p) (v : ℝ) (hv : 0<v) :
    Integrable (fun z : ComplexSample (m := d+(n+1)) (n := n+1) =>
      ((complexNoncentralSampleSmallestEigenvalue M (Nat.succ_pos n) (Real.sqrt v • z))⁻¹)^p)
      (stdGaussian _) ↔ p<((d+1 : ℕ) : ℝ) := by
  let M' : Matrix (Fin (d+(n+1))) (Fin (n+1)) ℂ := (((Real.sqrt v)⁻¹ : ℝ) : ℂ) • M
  have he : (fun z : ComplexSample (m := d+(n+1)) (n := n+1) =>
      ((complexNoncentralSampleSmallestEigenvalue M (Nat.succ_pos n) (Real.sqrt v • z))⁻¹)^p) =
      (fun z => (v⁻¹)^p*(actualNoncentralInverseMinimum d n M' z)^p) := by
    funext z
    have hmin : 0≤complexNoncentralSampleSmallestEigenvalue M' (Nat.succ_pos n) z :=
      complexNoncentralGram_eigenvalues₀_nonneg M' z _
    rw [noncentralSampleMinimum_amplitude_scale _ _ _ (Real.sqrt_pos.mpr hv),
      Real.sq_sqrt hv.le,_root_.mul_inv_rev]
    rw [Real.mul_rpow (inv_nonneg.mpr hmin) (inv_nonneg.mpr hv.le)]
    simp only [actualNoncentralInverseMinimum,M',mul_comm]
  rw [he,integrable_const_mul_iff
    (isUnit_iff_ne_zero.mpr (ne_of_gt (Real.rpow_pos_of_pos (inv_pos.mpr hv) p)))]
  exact actualNoncentralInverseMinimum_realMoment_integrable_iff d n M' p hp

end
end JinWishart
#print axioms JinWishart.actualNoncentralInverseMinimum_realMoment_integrable_iff
#print axioms JinWishart.actualNoncentralRectangular_inverseMinimum_realMoment_integrable_iff
#print axioms JinWishart.actualNoncentralInverseMinimum_realMoment_lintegral_eq_top
#print axioms JinWishart.actualNoncentralCovariance_inverseMinimum_realMoment_integrable_iff
