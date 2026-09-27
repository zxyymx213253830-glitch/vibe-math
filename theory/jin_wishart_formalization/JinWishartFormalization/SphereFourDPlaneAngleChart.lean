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

theorem polarCoord_symm_re (r θ : ℝ) :
    (Complex.polarCoord.symm (r, θ)).re = r * Real.cos θ := by
  rw [Complex.polarCoord_symm_apply]
  simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im,
    zero_mul, mul_zero, zero_add, one_mul, sub_zero]
  ring

theorem polarCoord_symm_im (r θ : ℝ) :
    (Complex.polarCoord.symm (r, θ)).im = r * Real.sin θ := by
  rw [Complex.polarCoord_symm_apply]
  simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im,
    zero_mul, mul_zero, zero_add, one_mul]
  ring

theorem polarCoord_symm_im_pos_iff (r θ : ℝ) (hr : 0 < r)
    (hlo : -Real.pi < θ) (hhi : θ < Real.pi) :
    0 < (Complex.polarCoord.symm (r, θ)).im ↔ 0 < θ ∧ θ < Real.pi := by
  rw [polarCoord_symm_im, mul_pos_iff_of_pos_left hr]
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

private def positiveHalfPlaneComplexIntegrand (F : ℝ × ℝ → ℝ) (z : ℂ) : ℝ :=
  if 0 < z.im then F (z.re, z.im) else 0

def fourDAngularPlaneWeightedIntegrand (κ : ℝ) (p : ℝ × ℝ) : ℝ :=
  (4 * Real.pi) * p.2 ^ 2 * fourDAngularPlaneSlice κ p.1 p.2

theorem fourDAngularPlaneWeightedIntegrand_polar_eq
    (κ r θ : ℝ) (hr : 0 < r) (hlo : -Real.pi < θ)
    (hhi : θ < Real.pi) :
    r * positiveHalfPlaneComplexIntegrand
        (fourDAngularPlaneWeightedIntegrand κ)
        (Complex.polarCoord.symm (r, θ)) =
      if 0 < θ ∧ θ < Real.pi then
        if r < 1 then
          (4 * Real.pi) * r ^ 3 * Real.sin θ ^ 2 * Real.exp (κ * Real.cos θ)
        else 0
      else 0 := by
  let z : ℂ := Complex.polarCoord.symm (r, θ)
  have hre : z.re = r * Real.cos θ := polarCoord_symm_re r θ
  have him : z.im = r * Real.sin θ := polarCoord_symm_im r θ
  by_cases hθ : 0 < θ ∧ θ < Real.pi
  · have hzpos : 0 < z.im :=
      (polarCoord_symm_im_pos_iff r θ hr hlo hhi).2 hθ
    change r * (if 0 < z.im then
      fourDAngularPlaneWeightedIntegrand κ (z.re, z.im) else 0) = _
    rw [if_pos hzpos]
    simp only [fourDAngularPlaneWeightedIntegrand]
    rw [hre, him]
    rw [fourDAngularPlaneSlice_polar_eq κ r θ hr hθ.1 hθ.2]
    by_cases hcut : r < 1 <;> simp [hθ, hcut] <;> ring
  · have hznot : ¬ 0 < z.im := by
      intro hz
      exact hθ ((polarCoord_symm_im_pos_iff r θ hr hlo hhi).1 hz)
    change r * (if 0 < z.im then
      fourDAngularPlaneWeightedIntegrand κ (z.re, z.im) else 0) = _
    simp [hznot, hθ]

/-- The plane set integral is the corresponding complex-plane integral with
the integrand extended by zero below the real axis. -/
theorem integral_upperHalfPlane_eq_complex (F : ℝ × ℝ → ℝ) :
    (∫ p in Set.univ ×ˢ Ioi (0 : ℝ), F p
      ∂((volume : Measure ℝ).prod (volume : Measure ℝ))) =
      ∫ z, positiveHalfPlaneComplexIntegrand F z := by
  let H : Set (ℝ × ℝ) := Set.univ ×ˢ Ioi (0 : ℝ)
  have hH : MeasurableSet H := by
    dsimp [H]
    exact MeasurableSet.prod MeasurableSet.univ measurableSet_Ioi
  calc
    _ = ∫ p, H.indicator F p ∂((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
      rw [← integral_indicator hH]
    _ = ∫ p, (if 0 < p.2 then F p else 0)
        ∂((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
      congr 1
      funext p
      simp [H, Set.indicator_apply, mem_prod]
    _ = ∫ z, (if 0 < (Complex.measurableEquivRealProd z).2 then
        F (Complex.measurableEquivRealProd z) else 0) := by
      symm
      exact Complex.volume_preserving_equiv_real_prod.integral_comp
        Complex.measurableEquivRealProd.measurableEmbedding
        (fun p : ℝ × ℝ => if 0 < p.2 then F p else 0)
    _ = ∫ z, positiveHalfPlaneComplexIntegrand F z := by
      apply integral_congr_ae
      filter_upwards with z
      simp [positiveHalfPlaneComplexIntegrand,
        Complex.measurableEquivRealProd]

/-- Actual Mathlib complex-polar change of variables for the weighted angular
test. The upper-half-plane cutoff becomes the single angular chart `(0,π)`;
the radial cutoff remains `r < 1`. -/
theorem integral_fourDAngularPlaneWeightedComplex_eq_angleChart (κ : ℝ) :
    (∫ z, positiveHalfPlaneComplexIntegrand
      (fourDAngularPlaneWeightedIntegrand κ) z) =
      ∫ p in Complex.polarCoord.target,
        if 0 < p.2 ∧ p.2 < Real.pi then
          if p.1 < 1 then
            (4 * Real.pi) * p.1 ^ 3 * Real.sin p.2 ^ 2 *
              Real.exp (κ * Real.cos p.2)
          else 0
        else 0 := by
  rw [← Complex.integral_comp_polarCoord_symm
    (positiveHalfPlaneComplexIntegrand (fourDAngularPlaneWeightedIntegrand κ))]
  apply setIntegral_congr_fun Complex.polarCoord.open_target.measurableSet
  intro p hp
  have hp' : 0 < p.1 ∧ -Real.pi < p.2 ∧ p.2 < Real.pi := by
    simpa only [Complex.polarCoord_target, mem_prod, mem_Ioi, mem_Ioo] using hp
  have hpoint := fourDAngularPlaneWeightedIntegrand_polar_eq
    κ p.1 p.2 hp'.1 hp'.2.1 hp'.2.2
  simpa only [smul_eq_mul] using hpoint

private def fourDAngularAngleChartIntegrand (κ : ℝ) (p : ℝ × ℝ) : ℝ :=
  if 0 < p.2 ∧ p.2 < Real.pi then
    if p.1 < 1 then
      (4 * Real.pi) * p.1 ^ 3 * Real.sin p.2 ^ 2 *
        Real.exp (κ * Real.cos p.2)
    else 0
  else 0

private def fourDAngularAngleRectangleIntegrand (κ : ℝ) (p : ℝ × ℝ) : ℝ :=
  (4 * Real.pi) * p.1 ^ 3 * Real.sin p.2 ^ 2 *
    Real.exp (κ * Real.cos p.2)

private def fourDAngularPositiveSubtypeIntegrand (κ : ℝ)
    (p : ℝ × Ioi (0 : ℝ)) : ℝ :=
  (4 * Real.pi) * (p.2 : ℝ) ^ 2 * fourDAngularPlaneSlice κ p.1 p.2

private theorem measurable_fourDAngularPositiveSubtypeIntegrand (κ : ℝ) :
    Measurable (fourDAngularPositiveSubtypeIntegrand κ) := by
  have hzero (p : ℝ × Ioi (0 : ℝ)) :
      ¬(p.1 = 0 ∧ (p.2 : ℝ) = 0) := by
    rintro ⟨_, h⟩
    exact (ne_of_gt p.2.property) h
  have hcut : MeasurableSet {p : ℝ × Ioi (0 : ℝ) |
      Real.sqrt (p.1 ^ 2 + (p.2 : ℝ) ^ 2) < 1} := by
    have hm : Measurable (fun p : ℝ × Ioi (0 : ℝ) =>
        Real.sqrt (p.1 ^ 2 + (p.2 : ℝ) ^ 2)) := by fun_prop
    exact hm measurableSet_Iio
  have hbranch : Measurable (fun p : ℝ × Ioi (0 : ℝ) =>
      if Real.sqrt (p.1 ^ 2 + (p.2 : ℝ) ^ 2) < 1 then
        (4 * Real.pi) * (p.2 : ℝ) ^ 2 *
          Real.exp (κ * (p.1 / Real.sqrt (p.1 ^ 2 + (p.2 : ℝ) ^ 2)))
      else 0) := by
    apply Measurable.ite hcut
    · fun_prop
    · exact measurable_const
  have heq : fourDAngularPositiveSubtypeIntegrand κ = fun p =>
      if Real.sqrt (p.1 ^ 2 + (p.2 : ℝ) ^ 2) < 1 then
        (4 * Real.pi) * (p.2 : ℝ) ^ 2 *
          Real.exp (κ * (p.1 / Real.sqrt (p.1 ^ 2 + (p.2 : ℝ) ^ 2)))
      else 0 := by
    funext p
    simp [fourDAngularPositiveSubtypeIntegrand, fourDAngularPlaneSlice,
      hzero p]
  rw [heq]
  exact hbranch

private theorem fourDAngularPositiveSubtypeIntegrand_norm_le (κ : ℝ)
    (p : ℝ × Ioi (0 : ℝ)) :
    ‖fourDAngularPositiveSubtypeIntegrand κ p‖ ≤
      (4 * Real.pi) * Real.exp |κ| := by
  dsimp [fourDAngularPositiveSubtypeIntegrand, fourDAngularPlaneSlice]
  have hpi : 0 ≤ 4 * Real.pi := by positivity
  have hr : 0 < (p.2 : ℝ) := p.2.property
  have hzero : ¬(p.1 = 0 ∧ (p.2 : ℝ) = 0) := by
    rintro ⟨_, h⟩
    exact (ne_of_gt hr) h
  by_cases hcut : Real.sqrt (p.1 ^ 2 + (p.2 : ℝ) ^ 2) < 1
  ·
    have hnorm : (p.2 : ℝ) ^ 2 ≤ 1 := by
      have hle : (p.2 : ℝ) ≤ Real.sqrt (p.1 ^ 2 + (p.2 : ℝ) ^ 2) :=
        Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg p.1])
      nlinarith
    have hsum : 0 < p.1 ^ 2 + (p.2 : ℝ) ^ 2 := by positivity
    have hden : 0 < Real.sqrt (p.1 ^ 2 + (p.2 : ℝ) ^ 2) :=
      Real.sqrt_pos.2 hsum
    have hratio : |p.1 / Real.sqrt (p.1 ^ 2 + (p.2 : ℝ) ^ 2)| ≤ 1 := by
      rw [abs_div, abs_of_pos hden]
      apply (div_le_one hden).2
      exact Real.abs_le_sqrt (by nlinarith [sq_nonneg (p.2 : ℝ)])
    have hexp : |Real.exp (κ * (p.1 /
        Real.sqrt (p.1 ^ 2 + (p.2 : ℝ) ^ 2)))| ≤ Real.exp |κ| := by
      rw [abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      calc
        κ * (p.1 / Real.sqrt (p.1 ^ 2 + (p.2 : ℝ) ^ 2)) ≤
            |κ * (p.1 / Real.sqrt (p.1 ^ 2 + (p.2 : ℝ) ^ 2))| := le_abs_self _
        _ = |κ| * |p.1 / Real.sqrt (p.1 ^ 2 + (p.2 : ℝ) ^ 2)| := abs_mul _ _
        _ ≤ |κ| := by nlinarith [abs_nonneg κ, hratio]
    rw [if_neg hzero, if_pos hcut]
    have hweight : |(4 * Real.pi) * (p.2 : ℝ) ^ 2| ≤ 4 * Real.pi := by
      rw [abs_mul, abs_of_nonneg hpi, abs_of_nonneg (sq_nonneg _)]
      nlinarith
    calc
      |(4 * Real.pi) * (p.2 : ℝ) ^ 2 *
          Real.exp (κ * (p.1 / Real.sqrt (p.1 ^ 2 + (p.2 : ℝ) ^ 2)))| =
          |(4 * Real.pi) * (p.2 : ℝ) ^ 2| *
            |Real.exp (κ * (p.1 / Real.sqrt (p.1 ^ 2 + (p.2 : ℝ) ^ 2)))| := by
        rw [abs_mul]
      _ ≤ (4 * Real.pi) * Real.exp |κ| :=
        mul_le_mul hweight hexp (abs_nonneg _) (by positivity)
      _ = (4 * Real.pi) * Real.exp |κ| := rfl
  · simp [hzero, hcut]
    positivity

private def fourDAngularPlaneAmbientIntegrand (κ : ℝ) (p : ℝ × ℝ) : ℝ :=
  if 0 < p.2 then fourDAngularPlaneWeightedIntegrand κ p else 0

private theorem measurable_fourDAngularPlaneAmbientIntegrand (κ : ℝ) :
    Measurable (fourDAngularPlaneAmbientIntegrand κ) := by
  have hslice : Measurable (fun p : ℝ × ℝ =>
      fourDAngularPlaneSlice κ p.1 p.2) := by
    unfold fourDAngularPlaneSlice
    refine Measurable.ite (by measurability) measurable_const ?_
    refine Measurable.ite (by measurability) ?_ measurable_const
    fun_prop
  unfold fourDAngularPlaneAmbientIntegrand fourDAngularPlaneWeightedIntegrand
  apply Measurable.ite (by measurability)
  · exact (measurable_const.mul (measurable_snd.pow_const _)).mul hslice
  · exact measurable_const

private theorem fourDAngularPlaneAmbientIntegrand_norm_le (κ : ℝ)
    (p : ℝ × ℝ) :
    ‖fourDAngularPlaneAmbientIntegrand κ p‖ ≤
      (4 * Real.pi) * Real.exp |κ| := by
  by_cases hy : 0 < p.2
  · have h := fourDAngularPositiveSubtypeIntegrand_norm_le κ
      (p.1, ⟨p.2, hy⟩)
    simpa [fourDAngularPlaneAmbientIntegrand,
      fourDAngularPositiveSubtypeIntegrand,
      fourDAngularPlaneWeightedIntegrand, hy] using h
  · simp [fourDAngularPlaneAmbientIntegrand, hy]
    positivity

private theorem integrable_fourDAngularPlaneAmbientIntegrand (κ : ℝ) :
    Integrable (fourDAngularPlaneAmbientIntegrand κ)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
  let K : Set (ℝ × ℝ) := Icc (-1 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  have hKcompact : IsCompact K := by
    dsimp [K]
    exact isCompact_Icc.prod isCompact_Icc
  have hKfinite : ((volume : Measure ℝ).prod (volume : Measure ℝ)) K ≠ ⊤ :=
    hKcompact.measure_ne_top
  have hmeas := measurable_fourDAngularPlaneAmbientIntegrand κ
  have hbound : ∀ᵐ p ∂(((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict K),
      ‖fourDAngularPlaneAmbientIntegrand κ p‖ ≤ (4 * Real.pi) * Real.exp |κ| :=
    Filter.Eventually.of_forall fun p => fourDAngularPlaneAmbientIntegrand_norm_le κ p
  have hion : IntegrableOn (fourDAngularPlaneAmbientIntegrand κ) K
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    Measure.integrableOn_of_bounded hKfinite hmeas.aestronglyMeasurable hbound
  have hzero_outside : ∀ p, p ∉ K → fourDAngularPlaneAmbientIntegrand κ p = 0 := by
    rintro ⟨s, r⟩ hp
    by_contra hne
    have hr : 0 < r := by
      by_contra hn
      have hnonpos : ¬ 0 < r := hn
      simp [fourDAngularPlaneAmbientIntegrand, hnonpos] at hne
    have hcut : Real.sqrt (s ^ 2 + r ^ 2) < 1 := by
      by_contra hc
      have hzero : ¬(s = 0 ∧ r = 0) := by
        rintro ⟨_, hr0⟩
        linarith
      simp [fourDAngularPlaneAmbientIntegrand,
        fourDAngularPlaneWeightedIntegrand, fourDAngularPlaneSlice,
        hr, hzero, hc] at hne
    have hsabs : |s| ≤ Real.sqrt (s ^ 2 + r ^ 2) :=
      Real.abs_le_sqrt (by nlinarith [sq_nonneg r])
    have hrbound : r ≤ Real.sqrt (s ^ 2 + r ^ 2) :=
      Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg s])
    have hslo : -1 ≤ s := by nlinarith [abs_le.mp hsabs]
    have hshi : s ≤ 1 := by nlinarith [abs_le.mp hsabs]
    have hrhi : r ≤ 1 := by nlinarith
    have hmem : (s, r) ∈ K := by
      simp only [K, mem_prod, mem_Icc]
      exact ⟨⟨hslo, hshi⟩, ⟨le_of_lt hr, hrhi⟩⟩
    exact hp hmem
  exact hion.integrable_of_forall_notMem_eq_zero hzero_outside

private theorem integrable_fourDAngularPositiveSubtypeIntegrand (κ : ℝ) :
    Integrable (fourDAngularPositiveSubtypeIntegrand κ)
      ((volume : Measure ℝ).prod
        (Measure.comap (Subtype.val : Ioi (0 : ℝ) → ℝ)
          (volume : Measure ℝ))) := by
  let e : MeasurableEmbedding
      (Prod.map (id : ℝ → ℝ) (Subtype.val : Ioi (0 : ℝ) → ℝ)) :=
    MeasurableEmbedding.id.prodMap
      (MeasurableEmbedding.subtype_coe measurableSet_Ioi)
  have hF : Integrable (fourDAngularPlaneAmbientIntegrand κ)
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict
        (Set.univ ×ˢ Ioi (0 : ℝ))) := by
    exact (integrable_fourDAngularPlaneAmbientIntegrand κ).mono_measure
      (Measure.restrict_le_self)
  have hmap : Measure.map
      (Prod.map (id : ℝ → ℝ) (Subtype.val : Ioi (0 : ℝ) → ℝ))
      ((volume : Measure ℝ).prod
        (Measure.comap (Subtype.val : Ioi (0 : ℝ) → ℝ)
          (volume : Measure ℝ))) =
      ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict
        (Set.univ ×ˢ Ioi (0 : ℝ)) :=
    map_product_volume_positiveSubtype
  have hcomp : Integrable
      (fourDAngularPlaneAmbientIntegrand κ ∘ fun p : ℝ × Ioi (0 : ℝ) =>
        (p.1, (p.2 : ℝ)))
      ((volume : Measure ℝ).prod
        (Measure.comap (Subtype.val : Ioi (0 : ℝ) → ℝ)
          (volume : Measure ℝ))) := by
    apply e.integrable_map_iff.mp
    rw [hmap]
    exact hF
  apply hcomp.congr
  filter_upwards with p
  have hp : 0 < (p.2 : ℝ) := p.2.property
  simp [Function.comp_apply, fourDAngularPositiveSubtypeIntegrand,
    fourDAngularPlaneAmbientIntegrand, fourDAngularPlaneWeightedIntegrand, hp]

/-- The actual Cartesian cutoff test is the integral of its positive-half-plane
weighted slice, before applying the planar polar-coordinate chart. -/
theorem fourDAngularCartesianTest_integral_eq_positiveHalfPlane (κ : ℝ) :
    (∫ x : EuclideanSpace ℝ (Fin 4), fourDAngularCartesianTest κ x
      ∂(volume : Measure (EuclideanSpace ℝ (Fin 4)))) =
      ∫ z, positiveHalfPlaneComplexIntegrand
        (fourDAngularPlaneWeightedIntegrand κ) z := by
  letI : SigmaFinite
      (Measure.comap (Subtype.val : Ioi (0 : ℝ) → ℝ) (volume : Measure ℝ)) :=
    SigmaFinite.of_map _ measurable_subtype_coe.aemeasurable (by
      rw [map_comap_subtype_coe measurableSet_Ioi]
      infer_instance)
  rw [fourDAngularCartesianTest_integral_eq_scalar_radial κ,
    fourDAngular_scalarRadial_eq_positiveHalfPlane κ]
  calc
    _ = ∫ p : ℝ × Ioi (0 : ℝ), fourDAngularPositiveSubtypeIntegrand κ p
        ∂((volume : Measure ℝ).prod
            (Measure.comap (Subtype.val : Ioi (0 : ℝ) → ℝ)
              (volume : Measure ℝ))) := by
      exact integral_integral
        (f := fun s r => fourDAngularPositiveSubtypeIntegrand κ (s, r))
        (integrable_fourDAngularPositiveSubtypeIntegrand κ)
    _ = ∫ p : ℝ × Ioi (0 : ℝ),
        fourDAngularPlaneWeightedIntegrand κ (p.1, p.2)
        ∂((volume : Measure ℝ).prod
          (Measure.comap (Subtype.val : Ioi (0 : ℝ) → ℝ)
            (volume : Measure ℝ))) := by
      apply integral_congr_ae
      filter_upwards with p
      rfl
    _ = ∫ p in Set.univ ×ˢ Ioi (0 : ℝ),
        fourDAngularPlaneWeightedIntegrand κ p
        ∂((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
      rw [integral_positiveSubtype_prod_eq_setIntegral]
    _ = ∫ z, positiveHalfPlaneComplexIntegrand
        (fourDAngularPlaneWeightedIntegrand κ) z :=
      integral_upperHalfPlane_eq_complex _

private theorem fourDAngularAngleRectangleIntegrand_continuous (κ : ℝ) :
    Continuous (fourDAngularAngleRectangleIntegrand κ) := by
  unfold fourDAngularAngleRectangleIntegrand
  fun_prop

private theorem fourDAngularAngleRectangleIntegrand_integrableOn
    (κ : ℝ) :
    IntegrableOn (fourDAngularAngleRectangleIntegrand κ)
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) Real.pi)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
  let K : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) Real.pi
  have hKcompact : IsCompact K := by
    dsimp [K]
    exact isCompact_Icc.prod isCompact_Icc
  have hsubset : Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) Real.pi ⊆ K := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    simp only [K, mem_prod, mem_Ioo, mem_Icc]
    exact ⟨⟨le_of_lt hr.1, le_of_lt hr.2⟩,
      ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩⟩
  have hcont : ContinuousOn (fourDAngularAngleRectangleIntegrand κ) K :=
    (fourDAngularAngleRectangleIntegrand_continuous κ).continuousOn
  exact hcont.integrableOn_of_subset_isCompact hKcompact
    (measurableSet_Ioo.prod measurableSet_Ioo) hsubset
    (ne_top_of_le_ne_top hKcompact.measure_ne_top (measure_mono hsubset))

/-- Reduces the complex polar target integral to the bounded radius-angle
rectangle. This is the product-integral stage; the final radial and angular
evaluation is separate. -/
theorem integral_fourDAngularPlaneAngleChart_eq_rectangle (κ : ℝ) :
    (∫ p in Complex.polarCoord.target,
      fourDAngularAngleChartIntegrand κ p) =
      ∫ r in Ioo (0 : ℝ) 1, ∫ θ in Ioo (0 : ℝ) Real.pi,
        fourDAngularAngleRectangleIntegrand κ (r, θ) := by
  let target : Set (ℝ × ℝ) := Complex.polarCoord.target
  let rect : Set (ℝ × ℝ) := Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) Real.pi
  have htarget : MeasurableSet target :=
    Complex.polarCoord.open_target.measurableSet
  have hrect : MeasurableSet rect := measurableSet_Ioo.prod measurableSet_Ioo
  have hindicator : target.indicator (fourDAngularAngleChartIntegrand κ) =
      rect.indicator (fourDAngularAngleRectangleIntegrand κ) := by
    classical
    funext p
    rcases p with ⟨r, θ⟩
    by_cases hr0 : 0 < r
    · by_cases hr1 : r < 1
      · by_cases hθ0 : 0 < θ
        · by_cases hθπ : θ < Real.pi
          · have hθlo : -Real.pi < θ := by linarith [Real.pi_pos]
            simp [Set.indicator_apply, fourDAngularAngleChartIntegrand,
              fourDAngularAngleRectangleIntegrand, target, rect,
              Complex.polarCoord_target, mem_prod, mem_Ioi, mem_Ioo,
              hr0, hr1, hθ0, hθπ, hθlo]
          · simp [Set.indicator_apply, fourDAngularAngleChartIntegrand,
              fourDAngularAngleRectangleIntegrand, target, rect,
              Complex.polarCoord_target, mem_prod, mem_Ioi, mem_Ioo,
              hr0, hr1, hθ0, hθπ]
        · simp [Set.indicator_apply, fourDAngularAngleChartIntegrand,
            fourDAngularAngleRectangleIntegrand, target, rect,
            Complex.polarCoord_target, mem_prod, mem_Ioi, mem_Ioo,
            hr0, hr1, hθ0]
      · simp [Set.indicator_apply, fourDAngularAngleChartIntegrand,
          fourDAngularAngleRectangleIntegrand, target, rect,
          Complex.polarCoord_target, mem_prod, mem_Ioi, mem_Ioo,
          hr0, hr1]
    · simp [Set.indicator_apply, fourDAngularAngleChartIntegrand,
        fourDAngularAngleRectangleIntegrand, target, rect,
        Complex.polarCoord_target, mem_prod, mem_Ioi, mem_Ioo, hr0]
  calc
    _ = ∫ p, target.indicator (fourDAngularAngleChartIntegrand κ) p := by
      rw [← integral_indicator htarget]
    _ = ∫ p, rect.indicator (fourDAngularAngleRectangleIntegrand κ) p := by
      rw [hindicator]
    _ = ∫ p in rect, fourDAngularAngleRectangleIntegrand κ p := by
      rw [integral_indicator hrect]
    _ = ∫ r in Ioo (0 : ℝ) 1, ∫ θ in Ioo (0 : ℝ) Real.pi,
        fourDAngularAngleRectangleIntegrand κ (r, θ) :=
      setIntegral_prod (fourDAngularAngleRectangleIntegrand κ)
        (fourDAngularAngleRectangleIntegrand_integrableOn κ)

private def fourDAngularAngleFactor (κ θ : ℝ) : ℝ :=
  Real.sin θ ^ 2 * Real.exp (κ * Real.cos θ)

private theorem integral_Ioo_cube_01 :
    (∫ r in Ioo (0 : ℝ) 1, r ^ 3) = (1 / 4 : ℝ) := by
  calc
    _ = ∫ r in Ioc (0 : ℝ) 1, r ^ 3 := by
      rw [← integral_Ioc_eq_integral_Ioo]
    _ = ∫ r in (0 : ℝ)..1, r ^ 3 := by
      rw [← intervalIntegral.integral_of_le (by norm_num)]
    _ = (1 / 4 : ℝ) := by
      rw [integral_pow]
      norm_num

private theorem integral_angleFactor_Ioo_eq_interval (κ : ℝ) :
    (∫ θ in Ioo (0 : ℝ) Real.pi, fourDAngularAngleFactor κ θ) =
      ∫ θ in (0 : ℝ)..Real.pi, fourDAngularAngleFactor κ θ := by
  calc
    _ = ∫ θ in Ioc (0 : ℝ) Real.pi, fourDAngularAngleFactor κ θ := by
      rw [← integral_Ioc_eq_integral_Ioo]
    _ = ∫ θ in (0 : ℝ)..Real.pi, fourDAngularAngleFactor κ θ := by
      rw [← intervalIntegral.integral_of_le (le_of_lt Real.pi_pos)]

/-- Fubini separation and the elementary `∫₀¹ r³ dr = 1/4` evaluation leave
exactly the claimed `π`-scaled single-angle integral. -/
theorem integral_fourDAngularAngleRectangle_eq_pi_angle (κ : ℝ) :
    (∫ r in Ioo (0 : ℝ) 1, ∫ θ in Ioo (0 : ℝ) Real.pi,
      fourDAngularAngleRectangleIntegrand κ (r, θ)) =
      Real.pi * ∫ θ in (0 : ℝ)..Real.pi, fourDAngularAngleFactor κ θ := by
  calc
    _ = ∫ r in Ioo (0 : ℝ) 1,
        (4 * Real.pi) * r ^ 3 *
          (∫ θ in Ioo (0 : ℝ) Real.pi, fourDAngularAngleFactor κ θ) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro r hr
      calc
        _ = ∫ θ in Ioo (0 : ℝ) Real.pi,
            ((4 * Real.pi) * r ^ 3) * fourDAngularAngleFactor κ θ := by
          apply setIntegral_congr_fun measurableSet_Ioo
          intro θ hθ
          simp [fourDAngularAngleRectangleIntegrand, fourDAngularAngleFactor]
          ring
        _ = _ := by rw [integral_const_mul]
    _ = (∫ θ in Ioo (0 : ℝ) Real.pi, fourDAngularAngleFactor κ θ) *
        ((4 * Real.pi) * ∫ r in Ioo (0 : ℝ) 1, r ^ 3) := by
      calc
        _ = ∫ r in Ioo (0 : ℝ) 1,
            (∫ θ in Ioo (0 : ℝ) Real.pi, fourDAngularAngleFactor κ θ) *
              ((4 * Real.pi) * r ^ 3) := by
          apply setIntegral_congr_fun measurableSet_Ioo
          intro r hr
          ring
        _ = (∫ θ in Ioo (0 : ℝ) Real.pi, fourDAngularAngleFactor κ θ) *
            (∫ r in Ioo (0 : ℝ) 1, (4 * Real.pi) * r ^ 3) := by
          rw [integral_const_mul]
        _ = _ := by rw [integral_const_mul]
    _ = Real.pi * ∫ θ in (0 : ℝ)..Real.pi, fourDAngularAngleFactor κ θ := by
      rw [integral_Ioo_cube_01, integral_angleFactor_Ioo_eq_interval]
      norm_num
      ring

/-- Combining the complex-polar change of variables, the rectangular chart
identification, and the radial `r^3` integral gives the exact single-angle
integral, with coefficient `π`. -/
theorem integral_fourDAngularPlaneWeightedComplex_eq_pi_angle (κ : ℝ) :
    (∫ z, positiveHalfPlaneComplexIntegrand
      (fourDAngularPlaneWeightedIntegrand κ) z) =
      Real.pi * ∫ θ in (0 : ℝ)..Real.pi,
        Real.exp (κ * Real.cos θ) * Real.sin θ ^ 2 := by
  calc
    _ = Real.pi * ∫ θ in (0 : ℝ)..Real.pi,
        fourDAngularAngleFactor κ θ := by
      rw [integral_fourDAngularPlaneWeightedComplex_eq_angleChart κ]
      change (∫ p in Complex.polarCoord.target,
          fourDAngularAngleChartIntegrand κ p) = _
      rw [integral_fourDAngularPlaneAngleChart_eq_rectangle κ,
        integral_fourDAngularAngleRectangle_eq_pi_angle κ]
    _ = Real.pi * ∫ θ in (0 : ℝ)..Real.pi,
        Real.exp (κ * Real.cos θ) * Real.sin θ ^ 2 := by
      congr 1
      apply intervalIntegral.integral_congr
      intro θ _
      dsimp [fourDAngularAngleFactor]
      ring_nf

/-- The complex-plane cutoff integral is one quarter of the established
`S³` single-angle chart integral. This exact factor is `π` versus `4π` in the
definition of the sphere chart. -/
theorem integral_fourDAngularPlaneWeightedComplex_eq_quarter_sphereChart
    (κ : ℝ) :
    (∫ z, positiveHalfPlaneComplexIntegrand
      (fourDAngularPlaneWeightedIntegrand κ) z) =
      (1 / 4 : ℝ) * fourDSphereExpAngleIntegralChart κ := by
  rw [integral_fourDAngularPlaneWeightedComplex_eq_pi_angle κ,
    fourDSphereExpAngleIntegralChart]
  ring

/-- The actual Mathlib `toSphere` angular integral agrees with the usual
single-angle `S³` chart integral. The proof compares both against the same
Cartesian cutoff integral and cancels the common radial mass `1/4`. -/
theorem fourDSphereToSphereIntegral_eq_chart (κ : ℝ) :
    (∫ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1,
      Real.exp (κ * (u : EuclideanSpace ℝ (Fin 4)) 0)
      ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).toSphere)) =
      fourDSphereExpAngleIntegralChart κ := by
  let cartesian : ℝ :=
    ∫ x : EuclideanSpace ℝ (Fin 4), fourDAngularCartesianTest κ x
      ∂(volume : Measure (EuclideanSpace ℝ (Fin 4)))
  let angular : ℝ :=
    ∫ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1,
      Real.exp (κ * (u : EuclideanSpace ℝ (Fin 4)) 0)
      ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).toSphere)
  have hCartesianChart : cartesian = (1 / 4 : ℝ) *
      fourDSphereExpAngleIntegralChart κ := by
    calc
      cartesian = ∫ z, positiveHalfPlaneComplexIntegrand
          (fourDAngularPlaneWeightedIntegrand κ) z := by
        dsimp [cartesian]
        exact fourDAngularCartesianTest_integral_eq_positiveHalfPlane κ
      _ = (1 / 4 : ℝ) * fourDSphereExpAngleIntegralChart κ :=
        integral_fourDAngularPlaneWeightedComplex_eq_quarter_sphereChart κ
  have hRadial :
      (∫ r : Ioi (0 : ℝ), fourDAngularRadialCutoff r
        ∂(Measure.volumeIoiPow
          (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) - 1))) =
        (1 / 4 : ℝ) := by
    simpa using fourDAngularRadialCutoff_integral
  have hCartesianSphere : cartesian = angular * (1 / 4 : ℝ) := by
    dsimp [cartesian, angular]
    rw [fourDAngularCartesianTest_integral_factor κ, hRadial]
  dsimp [angular]
  nlinarith [hCartesianChart, hCartesianSphere]

/-- For a center along the first coordinate axis, the squared distance from a
four-dimensional polar point expands into the radius, center amplitude, and
first spherical coordinate. This is the pointwise Gaussian exponent identity
needed to connect the actual shifted-ball probability to the angular theorem. -/
theorem fourDDistance_sq_sub_firstAxis (u : Metric.sphere
    (0 : EuclideanSpace ℝ (Fin 4)) 1) (r a : ℝ) :
    ‖r • (u : EuclideanSpace ℝ (Fin 4)) -
        a • EuclideanSpace.single (0 : Fin 4) (1 : ℝ)‖ ^ 2 =
      r ^ 2 + a ^ 2 - 2 * a * r * (u : EuclideanSpace ℝ (Fin 4)) 0 := by
  have hu : ‖(u : EuclideanSpace ℝ (Fin 4))‖ = 1 := by
    simpa [dist_eq_norm] using u.property
  rw [norm_sub_sq_real, norm_smul, norm_smul, hu]
  rw [real_inner_smul_left, real_inner_smul_right]
  simp [Real.norm_eq_abs, EuclideanSpace.inner_single_right]
  ring_nf

/-- The sphere integral of an axially shifted four-dimensional Gaussian shell
is the single-angle chart factor times its radial Gaussian exponential. -/
theorem fourDShiftedGaussianAngularIntegral_eq_chart (a r : ℝ) :
    (∫ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1,
      Real.exp (-‖r • (u : EuclideanSpace ℝ (Fin 4)) -
        a • EuclideanSpace.single (0 : Fin 4) (1 : ℝ)‖ ^ 2 / 2)
      ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).toSphere)) =
        Real.exp (-((r ^ 2 + a ^ 2) / 2)) *
          fourDSphereExpAngleIntegralChart (a * r) := by
  calc
    _ = ∫ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1,
        Real.exp (-((r ^ 2 + a ^ 2) / 2)) *
          Real.exp (a * r * (u : EuclideanSpace ℝ (Fin 4)) 0)
        ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).toSphere) := by
      apply integral_congr_ae
      filter_upwards with u
      rw [fourDDistance_sq_sub_firstAxis]
      have he : -(r ^ 2 + a ^ 2 - 2 * a * r *
          (u : EuclideanSpace ℝ (Fin 4)) 0) / 2 =
          -((r ^ 2 + a ^ 2) / 2) + a * r *
            (u : EuclideanSpace ℝ (Fin 4)) 0 := by ring
      rw [he, Real.exp_add]
    _ = Real.exp (-((r ^ 2 + a ^ 2) / 2)) *
        (∫ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1,
          Real.exp (a * r * (u : EuclideanSpace ℝ (Fin 4)) 0)
          ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).toSphere)) := by
      rw [integral_const_mul]
    _ = Real.exp (-((r ^ 2 + a ^ 2) / 2)) *
        fourDSphereExpAngleIntegralChart (a * r) := by
      rw [fourDSphereToSphereIntegral_eq_chart]

/-- After the four-dimensional polar Jacobian and Gaussian normalizer are
included, the actual axial Gaussian shell has the established `(2,1)` radial
kernel. This is the pointwise shell-to-Nuttall bridge. -/
theorem fourDShiftedGaussianShell_eq_radialKernel
    (a r : ℝ) (ha : 0 < a) (hr : 0 < r) :
    (2 * Real.pi)⁻¹ ^ 2 * r ^ 3 *
      (∫ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1,
        Real.exp (-‖r • (u : EuclideanSpace ℝ (Fin 4)) -
          a • EuclideanSpace.single (0 : Fin 4) (1 : ℝ)‖ ^ 2 / 2)
        ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).toSphere)) =
      noncentralChiFourRadialKernel a r := by
  rw [fourDShiftedGaussianAngularIntegral_eq_chart]
  simpa [mul_assoc] using
    shiftedGaussianFourDShellFactor_eq_nuttallKernel a r ha hr

end

end JinWishart
