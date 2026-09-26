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

/-- On Mathlib's principal polar chart, positive imaginary part is exactly the
single angular interval `(0, π)`. -/
theorem sin_pos_iff_angle_pos (θ : ℝ) (hlo : -Real.pi < θ)
    (hhi : θ < Real.pi) :
    0 < Real.sin θ ↔ 0 < θ ∧ θ < Real.pi := by
  constructor
  · intro hs
    constructor
    · by_contra hθ
      have hnonpos : Real.sin θ ≤ 0 :=
        Real.sin_nonpos_of_nonpos_of_neg_pi_le (le_of_not_gt hθ) (le_of_lt hlo)
      linarith
    · exact hhi
  · rintro ⟨hθ, hθπ⟩
    exact Real.sin_pos_of_pos_of_lt_pi hθ hθπ

theorem polarCoord_symm_im_pos_iff (r θ : ℝ) (hr : 0 < r)
    (hlo : -Real.pi < θ) (hhi : θ < Real.pi) :
    0 < (Complex.polarCoord.symm (r, θ)).im ↔ 0 < θ ∧ θ < Real.pi := by
  have him : (Complex.polarCoord.symm (r, θ)).im = r * Real.sin θ := by
    rw [Complex.polarCoord_symm_apply]
    simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, zero_add, one_mul]
    ring
  rw [him, mul_pos_iff_of_pos_left hr]
  exact sin_pos_iff_angle_pos θ hlo hhi

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

/-- Mapping the product of ordinary Lebesgue measure and the positive-subtype
Lebesgue measure into `ℝ × ℝ` gives the restriction to the upper half-plane. -/
theorem map_product_volume_positiveSubtype :
    Measure.map
        (Prod.map (id : ℝ → ℝ)
          (Subtype.val : Ioi (0 : ℝ) → ℝ))
        ((volume : Measure ℝ).prod
          (Measure.comap (Subtype.val : Ioi (0 : ℝ) → ℝ)
            (volume : Measure ℝ))) =
      ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict
        (Set.univ ×ˢ Ioi (0 : ℝ)) := by
  letI : SigmaFinite
      (Measure.comap (Subtype.val : Ioi (0 : ℝ) → ℝ) (volume : Measure ℝ)) :=
    SigmaFinite.of_map _ measurable_subtype_coe.aemeasurable (by
      rw [map_comap_subtype_coe measurableSet_Ioi]
      infer_instance)
  rw [← MeasureTheory.Measure.map_prod_map (volume : Measure ℝ)
    (Measure.comap (Subtype.val : Ioi (0 : ℝ) → ℝ) (volume : Measure ℝ))
    measurable_id measurable_subtype_coe]
  rw [MeasureTheory.Measure.map_id,
    map_comap_subtype_coe measurableSet_Ioi]
  rw [← MeasureTheory.Measure.prod_restrict (Set.univ : Set ℝ) (Ioi (0 : ℝ))]
  simp

/-- The positive-subtype product integral is the ordinary plane set integral
over the upper half-plane. This is a measure transport statement, not yet the
polar-coordinate change of variables. -/
theorem integral_positiveSubtype_prod_eq_setIntegral (F : ℝ × ℝ → ℝ) :
    (∫ p : ℝ × Ioi (0 : ℝ), F (p.1, p.2)
      ∂((volume : Measure ℝ).prod
        (Measure.comap (Subtype.val : Ioi (0 : ℝ) → ℝ) (volume : Measure ℝ)))) =
      ∫ p in Set.univ ×ˢ Ioi (0 : ℝ), F p
        ∂((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
  let e : MeasurableEmbedding
      (Prod.map (id : ℝ → ℝ) (Subtype.val : Ioi (0 : ℝ) → ℝ)) :=
    MeasurableEmbedding.id.prodMap
      (MeasurableEmbedding.subtype_coe measurableSet_Ioi)
  calc
    _ = ∫ p, F p ∂Measure.map
        (Prod.map (id : ℝ → ℝ) (Subtype.val : Ioi (0 : ℝ) → ℝ))
        ((volume : Measure ℝ).prod
          (Measure.comap (Subtype.val : Ioi (0 : ℝ) → ℝ) (volume : Measure ℝ))) := by
      symm
      exact e.integral_map F
    _ = ∫ p, F p ∂((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict
        (Set.univ ×ˢ Ioi (0 : ℝ)) := by
      rw [map_product_volume_positiveSubtype]
    _ = ∫ p in Set.univ ×ˢ Ioi (0 : ℝ), F p
        ∂((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
      rfl

end

end JinWishart
