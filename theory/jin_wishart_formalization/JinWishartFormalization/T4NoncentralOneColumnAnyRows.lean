import JinWishartFormalization.NoncentralOneColumnEnergy
import JinWishartFormalization.OneColumnFrobeniusParameter
import JinWishartFormalization.T4CentralOneColumnAnyRows

/-!
# Arbitrary-row noncentral one-column hard-edge asymptotic

For every positive row count `m` and every complex mean `M`, the actual
one-column Gram eigenvalue CDF satisfies
`F_M(x) / x^m → exp (-‖M‖_F²) / m!` as `x → 0+`.

On a ball of radius `R`, the shifted Gaussian density is bounded between
`exp (-‖μ‖²/2 ± R*‖μ‖)` times the centered density. Integrate these bounds
and squeeze using the already proved central hard-edge limit. This includes
zero mean and does not assume a candidate eigenvalue density or a Nuttall
formula. [需人工审查] The Gaussian model, density translation, integrability
on the compact ball, and the interpretation of the right-hand limit.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped InnerProductSpace

namespace JinWishart

noncomputable section

private theorem continuous_gaussianDensity {ι : Type*} [Fintype ι] :
    Continuous (euclideanStdGaussianDensity (ι := ι)) := by
  unfold euclideanStdGaussianDensity
  fun_prop

/-- Translation of a finite-dimensional standard Gaussian density, with the
likelihood ratio written explicitly in terms of the mean and inner product. -/
theorem euclideanStdGaussianDensity_sub {ι : Type*} [Fintype ι]
    (μ z : EuclideanSpace ℝ ι) :
    euclideanStdGaussianDensity (z - μ) =
      Real.exp (-(‖μ‖ ^ 2 / 2) + inner ℝ z μ) * euclideanStdGaussianDensity z := by
  unfold euclideanStdGaussianDensity
  rw [norm_sub_sq_real]
  rw [show -( (‖z‖ ^ 2 - 2 * inner ℝ z μ + ‖μ‖ ^ 2)) / 2 =
    (-(‖μ‖ ^ 2 / 2) + inner ℝ z μ) + (-(‖z‖ ^ 2) / 2) by ring]
  rw [Real.exp_add]
  ring

/-- Finite-radius comparison of shifted and centered Gaussian ball integrals.
The inequalities retain explicit exponential error factors. -/
theorem gaussian_shiftedBall_integral_bounds {ι : Type*} [Fintype ι]
    (μ : EuclideanSpace ℝ ι) (R : ℝ) :
    Real.exp (-(‖μ‖ ^ 2 / 2) - R * ‖μ‖) *
        (∫ z in Metric.closedBall (0 : EuclideanSpace ℝ ι) R,
          euclideanStdGaussianDensity z) ≤
      (∫ z in Metric.closedBall (0 : EuclideanSpace ℝ ι) R,
        euclideanStdGaussianDensity (z - μ)) ∧
    (∫ z in Metric.closedBall (0 : EuclideanSpace ℝ ι) R,
        euclideanStdGaussianDensity (z - μ)) ≤
      Real.exp (-(‖μ‖ ^ 2 / 2) + R * ‖μ‖) *
        (∫ z in Metric.closedBall (0 : EuclideanSpace ℝ ι) R,
          euclideanStdGaussianDensity z) := by
  classical
  let B := Metric.closedBall (0 : EuclideanSpace ℝ ι) R
  have hcompact : IsCompact B := isCompact_closedBall _ _
  have hcenter : IntegrableOn euclideanStdGaussianDensity B :=
    continuous_gaussianDensity.continuousOn.integrableOn_compact hcompact
  have hshift : IntegrableOn (fun z => euclideanStdGaussianDensity (z - μ)) B :=
    (continuous_gaussianDensity.comp (continuous_id.sub continuous_const)).continuousOn
      |>.integrableOn_compact hcompact
  have hinner (z : EuclideanSpace ℝ ι) (hz : z ∈ B) :
      -R * ‖μ‖ ≤ inner ℝ z μ ∧ inner ℝ z μ ≤ R * ‖μ‖ := by
    have hnorm : ‖z‖ ≤ R := by simpa [B, Metric.mem_closedBall, dist_eq_norm] using hz
    have habs : |inner ℝ z μ| ≤ R * ‖μ‖ :=
      (abs_real_inner_le_norm z μ).trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg μ))
    have h := abs_le.mp habs
    constructor <;> linarith [h.1, h.2]
  have hnonneg (z : EuclideanSpace ℝ ι) : 0 ≤ euclideanStdGaussianDensity z := by
    unfold euclideanStdGaussianDensity
    positivity
  constructor
  · rw [← integral_const_mul]
    apply setIntegral_mono_on (hcenter.const_mul _) hshift measurableSet_closedBall
    intro z hz
    rw [euclideanStdGaussianDensity_sub]
    exact mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (by linarith [(hinner z hz).1])) (hnonneg z)
  · rw [← integral_const_mul]
    apply setIntegral_mono_on hshift (hcenter.const_mul _) measurableSet_closedBall
    intro z hz
    rw [euclideanStdGaussianDensity_sub]
    exact mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (by linarith [(hinner z hz).2])) (hnonneg z)

/-- The same finite-radius bounds on the CDF of the actual complex Gaussian
Gram model. The reference CDF is the actual centered model. -/
theorem noncentralOneColumnCDF_bounds_by_central
    {m : ℕ} (hm : 0 < m) (M : Matrix (Fin m) (Fin 1) ℂ)
    (x : ℝ) (hx : 0 ≤ x) :
    let F := fun A : Matrix (Fin m) (Fin 1) ℂ =>
      cdf ((stdGaussian (ComplexSample (m := m) (n := 1))).map
        (complexNoncentralSampleSmallestEigenvalue A (by norm_num))) x
    Real.exp (-(‖complexSampleMean M‖ ^ 2 / 2) - Real.sqrt (2 * x) *
        ‖complexSampleMean M‖) * F 0 ≤ F M ∧
      F M ≤ Real.exp (-(‖complexSampleMean M‖ ^ 2 / 2) + Real.sqrt (2 * x) *
        ‖complexSampleMean M‖) * F 0 := by
  intro F
  have hzero : complexSampleMean (0 : Matrix (Fin m) (Fin 1) ℂ) = 0 := by
    ext ij
    simp [complexSampleMean]
  have hbase := noncentralColumnCDF_eq_shiftedGaussianDensityIntegral hm
    (0 : Matrix (Fin m) (Fin 1) ℂ) x hx
  simp only [hzero, sub_zero] at hbase
  have hnon := noncentralColumnCDF_eq_shiftedGaussianDensityIntegral hm M x hx
  change F 0 = ∫ z in Metric.closedBall (0 : ComplexSample (m := m) (n := 1))
    (Real.sqrt (2 * x)), euclideanStdGaussianDensity z at hbase
  change F M = ∫ z in Metric.closedBall (0 : ComplexSample (m := m) (n := 1))
    (Real.sqrt (2 * x)), euclideanStdGaussianDensity (z - complexSampleMean M) at hnon
  have h := gaussian_shiftedBall_integral_bounds (complexSampleMean M) (Real.sqrt (2 * x))
  rw [← hbase, ← hnon] at h
  exact h

/-- **Actual-model noncentral T4, arbitrary positive row count.** The centered
case is included; noncentrality is half the real encoded mean norm squared. -/
theorem noncentralOneColumnSmallestCDF_div_tendsto_factorial
    {m : ℕ} (hm : 0 < m) (M : Matrix (Fin m) (Fin 1) ℂ) :
    Tendsto (fun x : ℝ =>
      cdf ((stdGaussian (ComplexSample (m := m) (n := 1))).map
        (complexNoncentralSampleSmallestEigenvalue M (by norm_num))) x / x ^ m)
      (𝓝[>] 0) (𝓝 ((Nat.factorial m : ℝ)⁻¹ *
        Real.exp (-(‖complexSampleMean M‖ ^ 2 / 2)))) := by
  let F := fun A : Matrix (Fin m) (Fin 1) ℂ =>
    cdf ((stdGaussian (ComplexSample (m := m) (n := 1))).map
      (complexNoncentralSampleSmallestEigenvalue A (by norm_num)))
  let L := fun x : ℝ => Real.exp (-(‖complexSampleMean M‖ ^ 2 / 2) -
    Real.sqrt (2 * x) * ‖complexSampleMean M‖)
  let H := fun x : ℝ => Real.exp (-(‖complexSampleMean M‖ ^ 2 / 2) +
    Real.sqrt (2 * x) * ‖complexSampleMean M‖)
  have hL : Continuous L := by dsimp [L]; fun_prop
  have hH : Continuous H := by dsimp [H]; fun_prop
  have hcentral := centralOneColumnSmallestCDF_div_tendsto_factorial m hm
  have hlow : Tendsto (fun x => L x * (F 0 x / x ^ m)) (𝓝[>] 0)
      (𝓝 ((Nat.factorial m : ℝ)⁻¹ * Real.exp (-(‖complexSampleMean M‖ ^ 2 / 2)))) := by
    simpa [L, F, mul_comm] using
      ((hL.tendsto 0).mono_left nhdsWithin_le_nhds).mul hcentral
  have hupp : Tendsto (fun x => H x * (F 0 x / x ^ m)) (𝓝[>] 0)
      (𝓝 ((Nat.factorial m : ℝ)⁻¹ * Real.exp (-(‖complexSampleMean M‖ ^ 2 / 2)))) := by
    simpa [H, F, mul_comm] using
      ((hH.tendsto 0).mono_left nhdsWithin_le_nhds).mul hcentral
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have h := (noncentralOneColumnCDF_bounds_by_central hm M x (le_of_lt hx)).1
    have hd := div_le_div_of_nonneg_right h (pow_nonneg (le_of_lt hx) m)
    simpa [F, L, mul_div_assoc] using hd
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have h := (noncentralOneColumnCDF_bounds_by_central hm M x (le_of_lt hx)).2
    have hd := div_le_div_of_nonneg_right h (pow_nonneg (le_of_lt hx) m)
    simpa [F, H, mul_div_assoc] using hd

/-- The paper's complex Frobenius parameter: `lambda = sum_i ||M_i||²`.
The diversity exponent is `m`, and the exact coefficient is `exp(-lambda)/m!`. -/
theorem noncentralOneColumnSmallestCDF_div_tendsto_frobenius
    {m : ℕ} (hm : 0 < m) (M : Matrix (Fin m) (Fin 1) ℂ) :
    Tendsto (fun x : ℝ =>
      cdf ((stdGaussian (ComplexSample (m := m) (n := 1))).map
        (complexNoncentralSampleSmallestEigenvalue M (by norm_num))) x / x ^ m)
      (𝓝[>] 0) (𝓝 ((Nat.factorial m : ℝ)⁻¹ *
        Real.exp (-(∑ i : Fin m, ‖M i 0‖ ^ 2)))) := by
  simpa only [complexSampleMean_oneColumn_norm_sq_div_two] using
    noncentralOneColumnSmallestCDF_div_tendsto_factorial hm M

end

end JinWishart
