import JinWishartFormalization.SphereFourDPlanePolar
import Mathlib.Analysis.SpecialFunctions.PolarCoord

open MeasureTheory Set

namespace JinWishart

noncomputable section

/-- Pointwise evaluation of the radial slice in the positive half-plane polar
chart. The axis and the origin are excluded by the hypotheses. -/
theorem fourDAngularPlaneSlice_polar_eq
    (κ r θ : ℝ) (hr : 0 < r) (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    fourDAngularPlaneSlice κ (r * Real.cos θ) (r * Real.sin θ) =
      if r < 1 then Real.exp (κ * Real.cos θ) else 0 := by
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ hθπ
  have hrho : 0 < r * Real.sin θ := mul_pos hr hsin
  have hsum :
      (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
    calc
      (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 =
          r ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
      _ = r ^ 2 := by rw [Real.cos_sq_add_sin_sq]; ring
  have hrad :
      Real.sqrt ((r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2) = r := by
    rw [hsum, Real.sqrt_sq_eq_abs, abs_of_pos hr]
  have hzero :
      ¬(r * Real.cos θ = 0 ∧ r * Real.sin θ = 0) := by
    rintro ⟨_, h⟩
    exact (ne_of_gt hrho) h
  by_cases hcut : r < 1
  · have hd : r ≠ 0 := ne_of_gt hr
    have hratio : r * Real.cos θ / r = Real.cos θ := by
      field_simp [hd]
    simp only [fourDAngularPlaneSlice, if_neg hzero, if_pos hcut, hrad, hratio]
  · simp only [fourDAngularPlaneSlice, if_neg hzero, if_neg hcut, hrad]

/-- Including the planar polar Jacobian, the positive-half-plane integrand
becomes the expected radial-angle product. -/
theorem fourDAngularPlaneSlice_polar_jacobian
    (κ r θ : ℝ) (hr : 0 < r) (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    r * (r * Real.sin θ) ^ 2 *
        fourDAngularPlaneSlice κ (r * Real.cos θ) (r * Real.sin θ) =
      if r < 1 then
        r ^ 3 * Real.sin θ ^ 2 * Real.exp (κ * Real.cos θ)
      else 0 := by
  rw [fourDAngularPlaneSlice_polar_eq κ r θ hr hθ hθπ]
  by_cases hcut : r < 1 <;> simp [hcut] <;> ring

/-- Unfolding `volumeIoiPow 2` exposes the radial Jacobian as the ordinary
Lebesgue integral over the positive half-line. -/
theorem integral_volumeIoiPow_two_eq_Ioi (f : Ioi (0 : ℝ) → ℝ) :
    (∫ r, f r ∂(Measure.volumeIoiPow 2)) =
      ∫ r : Ioi (0 : ℝ), (r : ℝ) ^ 2 * f r
        ∂(Measure.comap Subtype.val (volume : Measure ℝ)) := by
  rw [Measure.volumeIoiPow, integral_withDensity_eq_integral_toReal_smul]
  · congr 1
    funext r
    simp only [ENNReal.toReal_ofReal (sq_nonneg (r : ℝ))]
    simp [smul_eq_mul]
  · fun_prop
  · filter_upwards with r
    simp

theorem integral_volumeIoiPow_two_eq_setIntegral (f : Ioi (0 : ℝ) → ℝ) :
    (∫ r, f r ∂(Measure.volumeIoiPow 2)) =
      ∫ r in Ioi (0 : ℝ),
        if hr : r ∈ Ioi (0 : ℝ) then r ^ 2 * f ⟨r, hr⟩ else 0 := by
  rw [integral_volumeIoiPow_two_eq_Ioi]
  let g : ℝ → ℝ := fun r =>
    if hr : r ∈ Ioi (0 : ℝ) then r ^ 2 * f ⟨r, hr⟩ else 0
  calc
    _ = ∫ r : Ioi (0 : ℝ), g r ∂(Measure.comap Subtype.val (volume : Measure ℝ)) := by
      congr 1
      funext r
      have hr : (r : ℝ) ∈ Ioi (0 : ℝ) := r.2
      simp only [g, dif_pos hr]
    _ = ∫ r in Ioi (0 : ℝ), g r :=
      integral_subtype_comap measurableSet_Ioi g

/-- The scalar/radial expression is the iterated Lebesgue integral on the
positive half-plane with its planar `ρ²` weight. The inner integral is still
written over a subtype, making the product-measure interface explicit. -/
theorem fourDAngular_scalarRadial_eq_positiveHalfPlane (κ : ℝ) :
    (∫ s : ℝ, 4 * Real.pi *
      ∫ r : Ioi (0 : ℝ), fourDAngularPlaneSlice κ s r
        ∂(Measure.volumeIoiPow 2) ∂(volume : Measure ℝ)) =
      ∫ s : ℝ, ∫ r : Ioi (0 : ℝ),
        (4 * Real.pi) * (r : ℝ) ^ 2 * fourDAngularPlaneSlice κ s r
        ∂(Measure.comap Subtype.val (volume : Measure ℝ))
        ∂(volume : Measure ℝ) := by
  apply integral_congr_ae
  filter_upwards with s
  rw [integral_volumeIoiPow_two_eq_Ioi]
  rw [← integral_const_mul]
  congr 1
  funext r
  ring

end

end JinWishart
