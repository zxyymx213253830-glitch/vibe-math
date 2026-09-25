import JinWishartFormalization.NoncentralScalarCDF
import JinWishartFormalization.GaussianRadialLaw

/-!
# Complex-coordinate bridge for the scalar noncentral Gaussian

The real two-coordinate Gaussian representation of a `1 × 1` complex
sample maps isometrically to the complex plane.  This file records the
deterministic mean under that map.
-/

open Matrix MeasureTheory ProbabilityTheory Set

namespace JinWishart

/-- The scalar complex mean in real Gaussian coordinates becomes `√2 M`. -/
theorem centralScalarToComplex_complexSampleMean
    (M : Matrix (Fin 1) (Fin 1) ℂ) :
    centralScalarToComplex (complexSampleMean M) =
      (Real.sqrt 2 : ℂ) * M 0 0 := by
  have hcoord (x : ComplexSample (m := 1) (n := 1)) :
      centralScalarToComplex x =
        (x ((0, 0), 0) : ℂ) + (x ((0, 0), 1) : ℂ) * Complex.I := by
    simp [centralScalarToComplex, centralScalarIndexEquiv,
      LinearIsometryEquiv.piLpCongrLeft_apply,
      Complex.orthonormalBasisOneI_repr_symm_apply, Equiv.piCongrLeft']
  rw [hcoord]
  simp only [complexSampleMean]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

/-- The translated ball event is preserved by the real-to-complex
isometry, including the exact `√2` scaling of the deterministic mean. -/
theorem scalarGaussian_shiftedBall_eq_complexBall
    (M : Matrix (Fin 1) (Fin 1) ℂ) (R : ℝ) :
    (stdGaussian (ComplexSample (m := 1) (n := 1)))
      (Metric.closedBall (-complexSampleMean M) R) =
    (stdGaussian ℂ)
      (Metric.closedBall (-((Real.sqrt 2 : ℂ) * M 0 0)) R) := by
  rw [← stdGaussian_map_centralScalarToComplex]
  rw [Measure.map_apply (centralScalarToComplex.continuous.measurable)
    measurableSet_closedBall]
  have hball := centralScalarToComplex.preimage_closedBall
    (-((Real.sqrt 2 : ℂ) * M 0 0)) R
  rw [hball]
  congr 1
  rw [← centralScalarToComplex_complexSampleMean M]
  simp

/-- The standard complex Gaussian ball probability is its radial-density
integral with the planar normalizing factor `1 / (2π)`. -/
theorem stdGaussian_complex_ball_real_eq_densityIntegral
    (μ : ℂ) (R : ℝ) :
    (stdGaussian ℂ).real (Metric.closedBall μ R) =
      ∫ z in Metric.closedBall μ R,
        (2 * Real.pi)⁻¹ * Real.exp (-(‖z‖ ^ 2) / 2) := by
  let f : ℂ → ℝ := fun z =>
    (2 * Real.pi)⁻¹ * Real.exp (-(‖z‖ ^ 2) / 2)
  have hf : Measurable (fun z : ℂ => ENNReal.ofReal (f z)) := by
    fun_prop
  have htop : ∀ᵐ z ∂(volume : Measure ℂ).restrict (Metric.closedBall μ R),
      ENNReal.ofReal (f z) < ⊤ := by
    filter_upwards [] with z
    exact ENNReal.ofReal_lt_top
  have h := setIntegral_withDensity_eq_setIntegral_toReal_smul
    (μ := (volume : Measure ℂ)) hf htop
    (fun _ : ℂ => (1 : ℝ)) measurableSet_closedBall
  have hf_nonneg (z : ℂ) : 0 ≤ f z := by
    dsimp [f]
    positivity
  simp only [ENNReal.toReal_ofReal (hf_nonneg _), smul_eq_mul, mul_one] at h
  rw [stdGaussian_complex_eq_radialDensity]
  simpa [f, measureReal_def, integral_const] using h

/-- Translate the integration domain of a planar Gaussian without changing
Lebesgue measure. -/
theorem integral_gaussian_shiftedBall_eq_centeredDisk
    (μ : ℂ) (R : ℝ) :
    (∫ z in Metric.closedBall (-μ) R,
      Real.exp (-(‖z‖ ^ 2) / 2)) =
      ∫ z in Metric.closedBall (0 : ℂ) R,
        Real.exp (-(‖z - μ‖ ^ 2) / 2) := by
  let s : Set ℂ := Metric.closedBall (-μ) R
  let f : ℂ → ℝ := fun z => Real.exp (-(‖z‖ ^ 2) / 2)
  let g : ℂ → ℝ := s.indicator f
  have htranslate := integral_add_left_eq_self (μ := (volume : Measure ℂ)) g (-μ)
  have hmem (z : ℂ) : -μ + z ∈ s ↔ z ∈ Metric.closedBall (0 : ℂ) R := by
    simp [s, Metric.mem_closedBall, dist_eq_norm]
  have hpoint (z : ℂ) :
      g (-μ + z) = (Metric.closedBall (0 : ℂ) R).indicator
        (fun w : ℂ => Real.exp (-(‖w - μ‖ ^ 2) / 2)) z := by
    simp only [g]
    by_cases hz : z ∈ Metric.closedBall (0 : ℂ) R
    · rw [Set.indicator_of_mem ((hmem z).mpr hz), Set.indicator_of_mem hz]
      simp [f, sub_eq_add_neg, add_comm]
    · simp [hz, (hmem z).not.mpr hz]
  calc
    _ = ∫ z, g z := by rw [integral_indicator measurableSet_closedBall]
    _ = ∫ z, g (-μ + z) := htranslate.symm
    _ = ∫ z, (Metric.closedBall (0 : ℂ) R).indicator
          (fun w : ℂ => Real.exp (-(‖w - μ‖ ^ 2) / 2)) z := by
      exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = _ := by rw [integral_indicator measurableSet_closedBall]

/-- The actual scalar noncentral Wishart CDF is a translated planar Gaussian
disk integral in complex coordinates. -/
theorem noncentralScalarCDF_eq_complexGaussianDiskIntegral
    (M : Matrix (Fin 1) (Fin 1) ℂ) (x : ℝ) (hx : 0 ≤ x) :
    cdf ((stdGaussian (ComplexSample (m := 1) (n := 1))).map
      (complexNoncentralSampleSmallestEigenvalue M (by norm_num))) x =
      ∫ z in Metric.closedBall (0 : ℂ) (Real.sqrt (2 * x)),
        (2 * Real.pi)⁻¹ *
          Real.exp (-(‖z - (Real.sqrt 2 : ℂ) * M 0 0‖ ^ 2) / 2) := by
  rw [noncentralScalarCDF_eq_shiftedBall M x hx]
  change (((stdGaussian (ComplexSample (m := 1) (n := 1)))
    (Metric.closedBall (-complexSampleMean M) (Real.sqrt (2 * x)))).toReal) = _
  rw [scalarGaussian_shiftedBall_eq_complexBall M]
  change (stdGaussian ℂ).real
    (Metric.closedBall (-((Real.sqrt 2 : ℂ) * M 0 0)) (Real.sqrt (2 * x))) = _
  rw [stdGaussian_complex_ball_real_eq_densityIntegral]
  rw [integral_const_mul, integral_const_mul]
  rw [integral_gaussian_shiftedBall_eq_centeredDisk]

end JinWishart
