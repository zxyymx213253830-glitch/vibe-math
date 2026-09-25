import JinWishartFormalization.ScalarNoncentralPolar
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Fubini form of the scalar noncentral polar integral

Starting from the polar-coordinate change of variables, this file restricts
the radial coordinate to a finite interval and writes the result as an
iterated integral over radius and angle.  The integrability argument uses
continuity on a compact rectangle.
-/

open MeasureTheory Set

namespace JinWishart

noncomputable section

/-- The shifted Gaussian density in polar coordinates, including the polar
Jacobian. -/
private def scalarPolarIntegrand (c : ℝ) (p : ℝ × ℝ) : ℝ :=
  p.1 * Real.exp (-(‖(p.1 : ℂ) * (Real.cos p.2 + Real.sin p.2 * Complex.I) -
    (c : ℂ)‖ ^ 2) / 2)

private theorem scalarPolarIntegrand_continuous (c : ℝ) :
    Continuous (scalarPolarIntegrand c) := by
  unfold scalarPolarIntegrand
  fun_prop

private theorem scalarPolarIntegrand_integrableOn_rectangle
    (c R : ℝ) (_hR : 0 ≤ R) :
    IntegrableOn (scalarPolarIntegrand c)
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
  have hcont : ContinuousOn (scalarPolarIntegrand c) K :=
    (scalarPolarIntegrand_continuous c).continuousOn
  exact hcont.integrableOn_of_subset_isCompact hKcompact
    (measurableSet_Ioc.prod measurableSet_Ioo) hrect
      (by
        exact ne_top_of_le_ne_top hKcompact.measure_ne_top (measure_mono hrect))

/-- The shifted Gaussian mass of a disk, in polar variables and then as a
radius-first product integral.  This is the Fubini infrastructure before the
angular integral is replaced by its modified-Bessel expression. -/
theorem integral_shiftedGaussian_closedBall_eq_polar_product
    (c R : ℝ) (hR : 0 ≤ R) :
    (∫ z in Metric.closedBall (0 : ℂ) R,
      Real.exp (-(‖z - (c : ℂ)‖ ^ 2) / 2)) =
      ∫ r in Ioc (0 : ℝ) R,
        ∫ θ in Ioo (-Real.pi) Real.pi,
          scalarPolarIntegrand c (r, θ) := by
  rw [integral_shiftedGaussian_closedBall_eq_polar]
  let rect : Set (ℝ × ℝ) := Ioc (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi
  let f : ℝ × ℝ → ℝ := scalarPolarIntegrand c
  let g : ℝ × ℝ → ℝ := fun p => p.1 *
    (if p.1 ≤ R then
      Real.exp (-(‖(p.1 : ℂ) * (Real.cos p.2 + Real.sin p.2 * Complex.I) -
        (c : ℂ)‖ ^ 2) / 2)
    else 0)
  have hmeas : MeasurableSet rect :=
    (measurableSet_Ioc.prod measurableSet_Ioo)
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
        simp [hc, hrect, g, f, scalarPolarIntegrand, hr,
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
        (scalarPolarIntegrand_integrableOn_rectangle c R hR)

/-- The angle integral of the polar kernel, expressed as a real factorial
series for `I₀`.  The passage from `Ioo` to the interval integral only changes
the two endpoints, which are null for Lebesgue measure. -/
theorem scalarPolar_angleIntegral_eq_realBesselSeries (r c : ℝ) :
    (∫ θ in Ioo (-Real.pi) Real.pi, scalarPolarIntegrand c (r, θ)) =
      r * (2 * Real.pi * Real.exp (-((r ^ 2 + c ^ 2) / 2)) *
        (∑' n : ℕ, ((r * c) ^ 2 / 4) ^ n / ((n.factorial : ℝ) ^ 2))) := by
  let q : ℝ → ℝ := fun θ =>
    Real.exp (-(‖(r : ℂ) * (Real.cos θ + Real.sin θ * Complex.I) -
      (c : ℂ)‖ ^ 2) / 2)
  have hIoo : (∫ θ in Ioo (-Real.pi) Real.pi, q θ) =
      ∫ θ in (-Real.pi)..Real.pi, q θ := by
    calc
      _ = ∫ θ in Ioc (-Real.pi) Real.pi, q θ :=
        integral_Ioc_eq_integral_Ioo.symm
      _ = ∫ θ in (-Real.pi)..Real.pi, q θ := by
        rw [← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  have hmul : (∫ θ in Ioo (-Real.pi) Real.pi,
      scalarPolarIntegrand c (r, θ)) =
      r * ∫ θ in Ioo (-Real.pi) Real.pi, q θ := by
    calc
      _ = ∫ θ in Ioo (-Real.pi) Real.pi, r * q θ := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro θ _
        simp [scalarPolarIntegrand, q]
      _ = _ := by rw [integral_const_mul]
  have hangleCast :
      (((∫ θ in Ioo (-Real.pi) Real.pi,
        scalarPolarIntegrand c (r, θ)) : ℝ) : ℂ) =
        (r : ℂ) *
          ((2 * Real.pi : ℂ) *
            (Real.exp (-((r ^ 2 + c ^ 2) / 2)) : ℂ) *
            modifiedBesselI 0 ((r * c : ℝ) : ℂ)) := by
    rw [hmul, hIoo, Complex.ofReal_mul]
    exact congrArg (fun x : ℂ => (r : ℂ) * x)
      (polarGaussian_angularIntegral_eq_besselI0 r c)
  have hseries := modifiedBesselI_zero_ofReal_eq_realSeries (r * c)
  have hcastSeries :
      (((∫ θ in Ioo (-Real.pi) Real.pi,
        scalarPolarIntegrand c (r, θ)) : ℝ) : ℂ) =
        ((r * (2 * Real.pi * Real.exp (-((r ^ 2 + c ^ 2) / 2)) *
          (∑' n : ℕ, ((r * c) ^ 2 / 4) ^ n /
            ((n.factorial : ℝ) ^ 2)))) : ℝ) := by
    rw [hangleCast, ← hseries]
    push_cast
    ring
  exact Complex.ofReal_injective hcastSeries

/-- The shifted Gaussian disk mass after performing the angular integral. -/
theorem integral_shiftedGaussian_closedBall_eq_bessel_radial
    (c R : ℝ) (hR : 0 ≤ R) :
    (∫ z in Metric.closedBall (0 : ℂ) R,
      Real.exp (-(‖z - (c : ℂ)‖ ^ 2) / 2)) =
      ∫ r in Ioc (0 : ℝ) R,
        r * (2 * Real.pi * Real.exp (-((r ^ 2 + c ^ 2) / 2)) *
          (∑' n : ℕ, ((r * c) ^ 2 / 4) ^ n / ((n.factorial : ℝ) ^ 2))) := by
  rw [integral_shiftedGaussian_closedBall_eq_polar_product c R hR]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro r _
  exact scalarPolar_angleIntegral_eq_realBesselSeries r c

end

end JinWishart
