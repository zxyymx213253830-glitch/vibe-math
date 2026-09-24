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

/-- Polar integration in any even-dimensional real inner product space. The
coefficient is expressed using the volume of the unit ball; this is the radial
integration tool needed for scalar central Wishart laws with arbitrary degrees
of freedom. -/
theorem integral_radial_even_dim {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E]
    [BorelSpace E] (k : ℕ) (hk : Module.finrank ℝ E = 2 * k)
    (f : ℝ → ℝ) :
    ∫ x : E, f ‖x‖ ∂volume =
      (2 * (k : ℝ) * ((Real.pi ^ k) / (Nat.factorial k : ℝ))) *
        ∫ r in Ioi (0 : ℝ), r ^ (2 * k - 1) * f r := by
  have hradial := MeasureTheory.integral_fun_norm_addHaar
    (μ := (volume : Measure E)) f
  have hball : (volume : Measure E).real (Metric.ball (0 : E) 1) =
      Real.pi ^ k / (Nat.factorial k : ℝ) := by
    rw [measureReal_def, InnerProductSpace.volume_ball_of_dim_even hk 0 1]
    simp [Nat.factorial_ne_zero]
    positivity
  rw [hk, hball] at hradial
  simpa [smul_eq_mul, Nat.cast_mul, Nat.cast_ofNat, mul_assoc, mul_left_comm,
    mul_comm] using hradial

/-- The even-dimensional radial formula restricted to a closed ball. This is
the form used to turn Gaussian ball probabilities into incomplete-Gamma
integrals. -/
theorem integral_radial_even_dim_closedBall {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E]
    [BorelSpace E] (k : ℕ) (hk : Module.finrank ℝ E = 2 * k)
    (R : ℝ) (hR : 0 ≤ R) (f : ℝ → ℝ) :
    ∫ x in Metric.closedBall (0 : E) R, f ‖x‖ ∂volume =
      (2 * (k : ℝ) * ((Real.pi ^ k) / (Nat.factorial k : ℝ))) *
        ∫ r in Ioc (0 : ℝ) R, r ^ (2 * k - 1) * f r := by
  let g : ℝ → ℝ := (Iic R).indicator f
  have hfun : (fun x : E ↦ g ‖x‖) =
      (Metric.closedBall (0 : E) R).indicator (fun x ↦ f ‖x‖) := by
    funext x
    simp [g, Set.indicator, Metric.closedBall, dist_eq_norm]
  rw [← MeasureTheory.integral_indicator measurableSet_closedBall, ← hfun]
  rw [integral_radial_even_dim k hk g]
  have hradial : (fun r : ℝ ↦ r ^ (2 * k - 1) * g r) =
      (Iic R).indicator (fun r ↦ r ^ (2 * k - 1) * f r) := by
    funext r
    by_cases hr : r ≤ R <;> simp [g, hr]
  rw [hradial, MeasureTheory.integral_indicator measurableSet_Iic]
  rw [Measure.restrict_restrict measurableSet_Iic, inter_comm]
  rw [show Ioi (0 : ℝ) ∩ Iic R = Ioc 0 R by ext r; simp]

end JinWishart
