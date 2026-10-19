import JinWishartFormalization.CentralMinimumRealPolynomial
import Mathlib.Analysis.Polynomial.Basic

/-!
# Exact leading right-tail asymptotic for every central rectangular minimum

Codex proofs. The finite polynomial representation and its monicity supply
the asymptotic; no spectral density or extra integrability premise is assumed.
[需人工审查] Interpretation of filters/limits and actual probability model.
-/
open Filter MeasureTheory ProbabilityTheory Asymptotics
open scoped Topology
namespace JinWishart
noncomputable section

theorem centralMinimumRealPolynomial_leading_limit (d n : ℕ) :
    Tendsto (fun x : ℝ => (centralMinimumRealPolynomial d n).eval x / x^(d*n))
      atTop (𝓝 1) := by
  have h := (centralMinimumRealPolynomial d n).isEquivalent_atTop_lead
  rw [(centralMinimumRealPolynomial_monic d n).leadingCoeff,
    centralMinimumRealPolynomial_natDegree] at h
  simp only [one_mul] at h
  apply (isEquivalent_iff_tendsto_one ?_).mp h
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact pow_ne_zero _ hx.ne'

theorem centralRectangularMinimumPolynomial_leading_limit (d n : ℕ) :
    Tendsto (fun x : ℝ => centralRectangularMinimumPolynomial d n x / x^(d*n))
      atTop (𝓝 ((centralDeterminantPowerMoment 0 n d)⁻¹)) := by
  have h := (centralMinimumRealPolynomial_leading_limit d n).const_mul
    ((centralDeterminantPowerMoment 0 n d)⁻¹)
  simpa only [mul_one,centralRectangularMinimumPolynomial_eq_realPolynomial,
    mul_div_assoc] using h

theorem actualCentralRectangular_minimum_right_tail_limit (d n : ℕ) (hn : 0 < n) :
    Tendsto (fun x : ℝ =>
      ((stdGaussian (ComplexSample (m := d+n) (n := n)))
        {z | x < centralGaussianSampleMinimum (d+n) n hn z}).toReal /
          (Real.exp (-(n : ℝ)*x) * x^(d*n)))
      atTop (𝓝 ((centralDeterminantPowerMoment 0 n d)⁻¹)) := by
  apply (centralRectangularMinimumPolynomial_leading_limit d n).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [actualCentralRectangular_minimum_tail d n hn x hx.le,
    ENNReal.toReal_ofReal (mul_nonneg (Real.exp_nonneg _)
      (centralRectangularMinimumPolynomial_nonneg d n x hx.le))]
  field_simp [Real.exp_ne_zero,pow_ne_zero _ hx.ne']

theorem actualCentralRectangular_covariance_right_tail_limit (d n : ℕ) (hn : 0 < n)
    (v : ℝ) (hv : 0 < v) :
    Tendsto (fun x : ℝ =>
      (1-((stdGaussian (ComplexSample (m := d+n) (n := n)))
        {z | centralGaussianSampleMinimum (d+n) n hn (Real.sqrt v • z) ≤ x}).toReal) /
          (Real.exp (-(n : ℝ)*(x/v)) * x^(d*n)))
      atTop (𝓝 ((centralDeterminantPowerMoment 0 n d)⁻¹ / v^(d*n))) := by
  have h := ((centralRectangularMinimumPolynomial_leading_limit d n).comp
    ((tendsto_div_const_atTop_of_pos hv).mpr tendsto_id)).div_const (v^(d*n))
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [actualCentralRectangular_covariance_minimum_CDF d n hn v hv x hx.le]
  dsimp only [Function.comp_apply]
  rw [div_pow]
  field_simp [Real.exp_ne_zero,pow_ne_zero _ hx.ne',pow_ne_zero _ hv.ne']
  simp only [id_eq,mul_comm,mul_left_comm,mul_assoc]
  ring

end
end JinWishart
#print axioms JinWishart.centralMinimumRealPolynomial_leading_limit
#print axioms JinWishart.centralRectangularMinimumPolynomial_leading_limit
#print axioms JinWishart.actualCentralRectangular_minimum_right_tail_limit
#print axioms JinWishart.actualCentralRectangular_covariance_right_tail_limit
