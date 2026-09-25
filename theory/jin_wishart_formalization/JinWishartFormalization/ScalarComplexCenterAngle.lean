import JinWishartFormalization.ScalarNoncentralPolar

/-!
# Angular Bessel identity for an arbitrary complex center

The angular integral depends on the center only through its modulus.  We
reduce to a real center by translating the full-period angle interval using
periodicity.
-/

open MeasureTheory Set

namespace JinWishart

/-- General complex-center polar distance expansion. -/
theorem polarPoint_sub_complex_norm_sq (r θ : ℝ) (μ : ℂ) :
    ‖(r : ℂ) * (Real.cos θ + Real.sin θ * Complex.I) - μ‖ ^ 2 =
      r ^ 2 + ‖μ‖ ^ 2 -
        2 * r * (μ.re * Real.cos θ + μ.im * Real.sin θ) := by
  rw [RCLike.norm_sq_eq_def]
  simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.cos_ofReal_re,
    Complex.sin_ofReal_re]
  have hnorm : ‖μ‖ ^ 2 = μ.re ^ 2 + μ.im ^ 2 := by
    simpa [pow_two] using (RCLike.norm_sq_eq_def (z := μ))
  nlinarith [hnorm, Real.sin_sq_add_cos_sq θ]

/-- For every complex center, the polar Gaussian's full-period angular
integral is the order-zero modified Bessel factor with amplitude `r * ‖μ‖`. -/
theorem polarGaussian_complexCenter_angleIntegral_eq_besselI0
    (r : ℝ) (μ : ℂ) :
    (((∫ θ in (-Real.pi)..Real.pi,
      Real.exp (-(‖(r : ℂ) * (Real.cos θ + Real.sin θ * Complex.I) - μ‖ ^ 2) / 2)) : ℝ) : ℂ) =
      (2 * Real.pi : ℂ) *
        (Real.exp (-((r ^ 2 + ‖μ‖ ^ 2) / 2)) : ℂ) *
          modifiedBesselI 0 ((r * ‖μ‖ : ℝ) : ℂ) := by
  by_cases hμ : μ = 0
  · subst μ
    simpa using polarGaussian_angularIntegral_eq_besselI0 r 0
  · let c : ℝ := ‖μ‖
    let φ : ℝ := Complex.arg μ
    have hnorm : c = ‖μ‖ := rfl
    have hc : 0 < c := norm_pos_iff.mpr hμ
    have hRe : c * Real.cos φ = μ.re := by
      simpa [c, φ] using Complex.norm_mul_cos_arg μ
    have hIm : c * Real.sin φ = μ.im := by
      simpa [c, φ] using Complex.norm_mul_sin_arg μ
    have hprojection (θ : ℝ) :
        μ.re * Real.cos θ + μ.im * Real.sin θ = c * Real.cos (θ - φ) := by
      rw [Real.cos_sub, ← hRe, ← hIm]
      ring
    have hpoint (θ : ℝ) :
        Real.exp (-(‖(r : ℂ) * (Real.cos θ + Real.sin θ * Complex.I) - μ‖ ^ 2) / 2) =
          Real.exp (-((r ^ 2 + c ^ 2) / 2)) *
            Real.exp (r * c * Real.cos (θ - φ)) := by
      rw [polarPoint_sub_complex_norm_sq, ← hnorm, hprojection]
      rw [show -(r ^ 2 + c ^ 2 - 2 * r * (c * Real.cos (θ - φ))) / 2 =
        -((r ^ 2 + c ^ 2) / 2) + r * c * Real.cos (θ - φ) by ring]
      rw [Real.exp_add]
    let F : ℝ → ℝ := fun θ => Real.exp (r * c * Real.cos θ)
    have hFperiodic : Function.Periodic F (2 * Real.pi) := by
      intro θ
      simp [F, Real.cos_add_two_pi]
    have hshift :
        (∫ θ in (-Real.pi)..Real.pi, F (θ - φ)) =
          ∫ θ in (-Real.pi)..Real.pi, F θ := by
      calc
        _ = ∫ θ in (-Real.pi + -φ)..(Real.pi + -φ), F θ := by
          simpa [sub_eq_add_neg] using
            (intervalIntegral.integral_comp_add_right (f := F) (-φ)
              (a := -Real.pi) (b := Real.pi))
        _ = ∫ θ in (-Real.pi)..Real.pi, F θ := by
          convert hFperiodic.intervalIntegral_add_eq (-Real.pi + -φ) (-Real.pi)
            using 1 <;> congr 1 <;> ring
    have hcomplex :
        (∫ θ in (-Real.pi)..Real.pi,
          Real.exp (-(‖(r : ℂ) * (Real.cos θ + Real.sin θ * Complex.I) - μ‖ ^ 2) / 2)) =
          Real.exp (-((r ^ 2 + c ^ 2) / 2)) *
            ∫ θ in (-Real.pi)..Real.pi, F θ := by
      calc
        _ = ∫ θ in (-Real.pi)..Real.pi,
            Real.exp (-((r ^ 2 + c ^ 2) / 2)) * F (θ - φ) := by
              apply intervalIntegral.integral_congr
              intro θ hθ
              simpa [F] using hpoint θ
        _ = Real.exp (-((r ^ 2 + c ^ 2) / 2)) *
            ∫ θ in (-Real.pi)..Real.pi, F (θ - φ) := by
              rw [intervalIntegral.integral_const_mul]
        _ = _ := by rw [hshift]
    have hrealPoint (θ : ℝ) :
        Real.exp (-(‖(r : ℂ) * (Real.cos θ + Real.sin θ * Complex.I) - (c : ℂ)‖ ^ 2) / 2) =
          Real.exp (-((r ^ 2 + c ^ 2) / 2)) * F θ := by
      rw [polarPoint_sub_real_norm_sq]
      rw [show -(r ^ 2 + c ^ 2 - 2 * r * c * Real.cos θ) / 2 =
        -((r ^ 2 + c ^ 2) / 2) + r * c * Real.cos θ by ring]
      simp [F, Real.exp_add]
    have hreal :
        (∫ θ in (-Real.pi)..Real.pi,
          Real.exp (-(‖(r : ℂ) * (Real.cos θ + Real.sin θ * Complex.I) - (c : ℂ)‖ ^ 2) / 2)) =
          Real.exp (-((r ^ 2 + c ^ 2) / 2)) *
            ∫ θ in (-Real.pi)..Real.pi, F θ := by
      calc
        _ = ∫ θ in (-Real.pi)..Real.pi,
            Real.exp (-((r ^ 2 + c ^ 2) / 2)) * F θ := by
              apply intervalIntegral.integral_congr
              intro θ hθ
              exact hrealPoint θ
        _ = _ := by rw [intervalIntegral.integral_const_mul]
    have hEq := hcomplex.trans hreal.symm
    rw [hEq]
    simpa [c, hnorm] using polarGaussian_angularIntegral_eq_besselI0 r c

end JinWishart
