import JinWishartFormalization.GaussianRadialLaw

/-!
# Finite-dimensional Gaussian density on shifted Euclidean balls

These lemmas turn the real Gaussian measure of a closed ball into an explicit
Lebesgue integral and translate that integral to a centered ball. They apply
to the four-dimensional real model underlying a two-row complex sample.
-/

open MeasureTheory Set ProbabilityTheory

namespace JinWishart

noncomputable section

/-- The real density factor for a standard Gaussian in a finite Euclidean
coordinate space. -/
def euclideanStdGaussianDensity {ι : Type*} [Fintype ι]
    (x : EuclideanSpace ℝ ι) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card ι *
    Real.exp (-(‖x‖ ^ 2) / 2)

/-- The probability of a closed ball under finite-dimensional standard
Gaussian measure is its explicit density integral. -/
theorem stdGaussian_euclidean_ball_real_eq_densityIntegral
    {ι : Type*} [Fintype ι] (μ : EuclideanSpace ℝ ι) (R : ℝ) :
    (stdGaussian (EuclideanSpace ℝ ι)).real (Metric.closedBall μ R) =
      ∫ x in Metric.closedBall μ R, euclideanStdGaussianDensity x := by
  let f : EuclideanSpace ℝ ι → ℝ := euclideanStdGaussianDensity
  have hfR : Measurable f := by
    change Measurable (fun z : EuclideanSpace ℝ ι =>
      (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card ι *
        Real.exp (-(‖z‖ ^ 2) / 2))
    fun_prop
  have hf : Measurable (fun z : EuclideanSpace ℝ ι => ENNReal.ofReal (f z)) :=
    hfR.ennreal_ofReal
  have htop : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ ι)).restrict
      (Metric.closedBall μ R), ENNReal.ofReal (f z) < ⊤ := by
    filter_upwards [] with z
    exact ENNReal.ofReal_lt_top
  have h := setIntegral_withDensity_eq_setIntegral_toReal_smul
    (μ := (volume : Measure (EuclideanSpace ℝ ι))) hf htop
    (fun _ : EuclideanSpace ℝ ι => (1 : ℝ)) measurableSet_closedBall
  have hf_nonneg (z : EuclideanSpace ℝ ι) : 0 ≤ f z := by
    dsimp [f, euclideanStdGaussianDensity]
    positivity
  simp only [ENNReal.toReal_ofReal (hf_nonneg _), smul_eq_mul, mul_one] at h
  rw [stdGaussian_euclidean_eq_radialDensity]
  simpa [f, euclideanStdGaussianDensity, measureReal_def, integral_const] using h

/-- Translation of a Gaussian density converts a ball centered at `-μ` into
the centered ball with shifted exponent. -/
theorem integral_euclideanGaussian_shiftedBall_eq_centered
    {ι : Type*} [Fintype ι] (μ : EuclideanSpace ℝ ι) (R : ℝ) :
    (∫ z in Metric.closedBall (-μ) R,
        euclideanStdGaussianDensity z) =
      ∫ z in Metric.closedBall (0 : EuclideanSpace ℝ ι) R,
        (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card ι *
          Real.exp (-‖z - μ‖ ^ 2 / 2) := by
  let s : Set (EuclideanSpace ℝ ι) := Metric.closedBall (-μ) R
  let f : EuclideanSpace ℝ ι → ℝ := euclideanStdGaussianDensity
  let g : EuclideanSpace ℝ ι → ℝ := s.indicator f
  have htranslate := integral_add_left_eq_self
    (μ := (volume : Measure (EuclideanSpace ℝ ι))) g (-μ)
  have hmem (z : EuclideanSpace ℝ ι) : -μ + z ∈ s ↔
      z ∈ Metric.closedBall (0 : EuclideanSpace ℝ ι) R := by
    simp [s, Metric.mem_closedBall, dist_eq_norm]
  have hpoint (z : EuclideanSpace ℝ ι) :
      g (-μ + z) = (Metric.closedBall (0 : EuclideanSpace ℝ ι) R).indicator
        (fun w : EuclideanSpace ℝ ι =>
          (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card ι *
            Real.exp (-‖w - μ‖ ^ 2 / 2)) z := by
    simp only [g]
    by_cases hz : z ∈ Metric.closedBall (0 : EuclideanSpace ℝ ι) R
    · rw [Set.indicator_of_mem ((hmem z).mpr hz), Set.indicator_of_mem hz]
      simp [f, euclideanStdGaussianDensity, sub_eq_add_neg, add_comm]
    · simp [hz, (hmem z).not.mpr hz]
  calc
    _ = ∫ z, g z := by rw [integral_indicator measurableSet_closedBall]
    _ = ∫ z, g (-μ + z) := htranslate.symm
    _ = ∫ z, (Metric.closedBall (0 : EuclideanSpace ℝ ι) R).indicator
          (fun w : EuclideanSpace ℝ ι =>
            (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card ι *
              Real.exp (-‖w - μ‖ ^ 2 / 2)) z := by
      exact integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = _ := by rw [integral_indicator measurableSet_closedBall]

end

end JinWishart
