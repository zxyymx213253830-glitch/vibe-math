import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Radial integration in the complex plane

This packages mathlib's generalized polar-coordinate theorem in the form needed
for the scalar complex-Gaussian Wishart case.  It is a geometric integration
lemma, not yet a statement about the Gaussian probability measure.
-/

open MeasureTheory Set

namespace JinWishart

theorem integral_complex_radial (f : ℝ → ℝ) :
    ∫ z : ℂ, f ‖z‖ ∂volume =
      2 * Real.pi * ∫ r in Ioi (0 : ℝ), r * f r := by
  have h := MeasureTheory.integral_fun_norm_addHaar (μ := (volume : Measure ℂ)) f
  rw [Complex.finrank_real_complex] at h
  have hball : (volume : Measure ℂ).real (Metric.ball (0 : ℂ) 1) = Real.pi := by
    simp [measureReal_def, Complex.volume_ball]
  rw [hball] at h
  simpa [smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using h

end JinWishart
