import JinWishartFormalization.ScalarComplexCenterAngle
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Disk integral for a general complex center

The proof changes to polar coordinates, applies Fubini on a finite
radius-angle rectangle, and evaluates the angle using the complex-center
order-zero Bessel identity.
-/

open MeasureTheory Set

namespace JinWishart

noncomputable section

private def complexCenterPolarIntegrand (μ : ℂ) (p : ℝ × ℝ) : ℝ :=
  p.1 * Real.exp (-(‖(p.1 : ℂ) * (Real.cos p.2 + Real.sin p.2 * Complex.I) - μ‖ ^ 2) / 2)

private theorem complexCenterPolarIntegrand_continuous (μ : ℂ) :
    Continuous (complexCenterPolarIntegrand μ) := by
  unfold complexCenterPolarIntegrand
  fun_prop

private theorem complexCenterPolarIntegrand_integrableOn_rectangle
    (μ : ℂ) (R : ℝ) (_hR : 0 ≤ R) :
    IntegrableOn (complexCenterPolarIntegrand μ)
      (Ioc (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi)
      (volume.prod volume) := by
  let K : Set (ℝ × ℝ) := Icc (0 : ℝ) R ×ˢ Icc (-Real.pi) Real.pi
  have hKcompact : IsCompact K := by
    dsimp [K]
    exact isCompact_Icc.prod isCompact_Icc
  have hrect : Ioc (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi ⊆ K := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    simp only [K, mem_prod]
    exact ⟨⟨le_of_lt hr.1, hr.2⟩, ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩⟩
  have hcont : ContinuousOn (complexCenterPolarIntegrand μ) K :=
    (complexCenterPolarIntegrand_continuous μ).continuousOn
  exact hcont.integrableOn_of_subset_isCompact hKcompact
    (measurableSet_Ioc.prod measurableSet_Ioo) hrect
      (by
        exact ne_top_of_le_ne_top hKcompact.measure_ne_top (measure_mono hrect))

/-- The disk integral for a general complex center, expressed as a radius-first
product integral over the polar chart. -/
theorem integral_shiftedGaussian_complex_closedBall_eq_polar_product
    (μ : ℂ) (R : ℝ) (hR : 0 ≤ R) :
    (∫ z in Metric.closedBall (0 : ℂ) R,
      Real.exp (-(‖z - μ‖ ^ 2) / 2)) =
      ∫ r in Ioc (0 : ℝ) R,
        ∫ θ in Ioo (-Real.pi) Real.pi,
          complexCenterPolarIntegrand μ (r, θ) := by
  rw [integral_shiftedGaussian_closedBall_eq_polar]
  let rect : Set (ℝ × ℝ) := Ioc (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi
  let f : ℝ × ℝ → ℝ := complexCenterPolarIntegrand μ
  let g : ℝ × ℝ → ℝ := fun p => p.1 *
    (if p.1 ≤ R then
      Real.exp (-(‖(p.1 : ℂ) * (Real.cos p.2 + Real.sin p.2 * Complex.I) - μ‖ ^ 2) / 2)
    else 0)
  have hmeas : MeasurableSet rect := measurableSet_Ioc.prod measurableSet_Ioo
  have htarget : MeasurableSet Complex.polarCoord.target :=
    Complex.polarCoord.open_target.measurableSet
  have hindicator :
      Complex.polarCoord.target.indicator g = rect.indicator f := by
    classical
    funext p
    simp only [Set.indicator_apply]
    by_cases hc : p ∈ Complex.polarCoord.target
    · by_cases hrect : p ∈ rect
      · have hr : p.1 ≤ R := hrect.1.2
        simp [hc, hrect, g, f, complexCenterPolarIntegrand, hr,
          Complex.polarCoord_symm_apply]
      · have hr : ¬ p.1 ≤ R := by
          intro hle
          apply hrect
          have hp' : 0 < p.1 ∧ -Real.pi < p.2 ∧ p.2 < Real.pi := by
            simpa only [Complex.polarCoord_target, mem_prod, mem_Ioi, mem_Ioo] using hc
          exact ⟨⟨hp'.1, hle⟩, hp'.2⟩
        simp [hc, hrect, g, hr]
    · by_cases hrect : p ∈ rect
      · have hc' : p ∈ Complex.polarCoord.target := by
          rw [Complex.polarCoord_target]
          exact ⟨hrect.1.1, hrect.2⟩
        exact (hc hc').elim
      · simp [hc, hrect]
  calc
    _ = ∫ p in Complex.polarCoord.target, g p := by
      apply setIntegral_congr_fun htarget
      intro p hp
      simp [g, Complex.polarCoord_symm_apply]
    _ = ∫ p, Complex.polarCoord.target.indicator g p := by
      rw [← integral_indicator htarget]
    _ = ∫ p, rect.indicator f p := by rw [hindicator]
    _ = ∫ p in rect, f p := by rw [integral_indicator hmeas]
    _ = ∫ r in Ioc (0 : ℝ) R, ∫ θ in Ioo (-Real.pi) Real.pi, f (r, θ) := by
      exact setIntegral_prod f
        (complexCenterPolarIntegrand_integrableOn_rectangle μ R hR)

/-- The open-angle set integral is the real Rice/Bessel factor; this is the
endpoint conversion needed to use the polar chart's angle interval. -/
theorem polarGaussian_complexCenter_angleSetIntegral_eq_realBessel
    (r : ℝ) (μ : ℂ) :
    (∫ θ in Ioo (-Real.pi) Real.pi,
      Real.exp (-(‖(r : ℂ) * (Real.cos θ + Real.sin θ * Complex.I) - μ‖ ^ 2) / 2)) =
      2 * Real.pi * Real.exp (-((r ^ 2 + ‖μ‖ ^ 2) / 2)) *
        (modifiedBesselI 0 ((r * ‖μ‖ : ℝ) : ℂ)).re := by
  have hinterval :
      (∫ θ in Ioo (-Real.pi) Real.pi,
        Real.exp (-(‖(r : ℂ) * (Real.cos θ + Real.sin θ * Complex.I) - μ‖ ^ 2) / 2)) =
        ∫ θ in (-Real.pi)..Real.pi,
          Real.exp (-(‖(r : ℂ) * (Real.cos θ + Real.sin θ * Complex.I) - μ‖ ^ 2) / 2) := by
    calc
      _ = ∫ θ in Ioc (-Real.pi) Real.pi,
          Real.exp (-(‖(r : ℂ) * (Real.cos θ + Real.sin θ * Complex.I) - μ‖ ^ 2) / 2) :=
            integral_Ioc_eq_integral_Ioo.symm
      _ = _ := by
        rw [← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  rw [hinterval]
  have hbessel := polarGaussian_complexCenter_angleIntegral_eq_besselI0 r μ
  rw [Complex.ofReal_exp] at hbessel
  have hre := congrArg Complex.re hbessel
  simp only [Complex.mul_re] at hre
  simp only [Complex.exp_ofReal_re, Complex.exp_ofReal_im,
    modifiedBesselI_zero_ofReal_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero] at hre
  simpa using hre

/-- The disk integral of a general complex-centered Gaussian is its one-
dimensional Rice radial integral. -/
theorem integral_shiftedGaussian_complex_closedBall_eq_riceRadial
    (μ : ℂ) (R : ℝ) (hR : 0 ≤ R) :
    (∫ z in Metric.closedBall (0 : ℂ) R,
      Real.exp (-(‖z - μ‖ ^ 2) / 2)) =
      ∫ r in Ioc (0 : ℝ) R,
        r * (2 * Real.pi * Real.exp (-((r ^ 2 + ‖μ‖ ^ 2) / 2)) *
          (modifiedBesselI 0 ((r * ‖μ‖ : ℝ) : ℂ)).re) := by
  rw [integral_shiftedGaussian_complex_closedBall_eq_polar_product μ R hR]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r _
  calc
    ∫ θ in Ioo (-Real.pi) Real.pi, complexCenterPolarIntegrand μ (r, θ) =
        r * ∫ θ in Ioo (-Real.pi) Real.pi,
          Real.exp (-(‖(r : ℂ) * (Real.cos θ + Real.sin θ * Complex.I) - μ‖ ^ 2) / 2) := by
            calc
              _ = ∫ θ in Ioo (-Real.pi) Real.pi,
                  r * Real.exp (-(‖(r : ℂ) * (Real.cos θ + Real.sin θ * Complex.I) - μ‖ ^ 2) / 2) := by
                    apply setIntegral_congr_fun measurableSet_Ioo
                    intro θ _
                    simp [complexCenterPolarIntegrand]
              _ = _ := by rw [integral_const_mul]
    _ = _ := by rw [polarGaussian_complexCenter_angleSetIntegral_eq_realBessel]

end

end JinWishart
