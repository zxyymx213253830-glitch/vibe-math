import JinWishartFormalization.SphereEightDAxialMeasure
import JinWishartFormalization.EightDimensionalAngularBesselI3
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import JinWishartFormalization.FourDimensionalPolarBridge
import JinWishartFormalization.SphereFourDPlaneAngleChart

open MeasureTheory Set

namespace JinWishart.EightDAxial

noncomputable section

local notation "E₈" => EuclideanSpace ℝ (Fin 8)
local notation "S₈" => Metric.sphere (0 : E₈) 1
local notation "E₇" => EuclideanSpace ℝ (Fin 7)

/-- Separate the axial real coordinate from the seven transverse ones. -/
noncomputable def euclideanEightToRealProdSeven : E₈ ≃ᵐ ℝ × E₇ :=
  (MeasurableEquiv.toLp 2 (Fin 8 → ℝ)).symm.trans <|
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 8 => ℝ) 0).trans <|
      MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.toLp 2 (Fin 7 → ℝ))

/-- The axial coordinate is preserved by the split. -/
theorem euclideanEightToRealProdSeven_symm_apply_zero (s : ℝ) (y : E₇) :
    (euclideanEightToRealProdSeven.symm (s, y) : E₈) 0 = s := by
  simp [euclideanEightToRealProdSeven, MeasurableEquiv.prodCongr]

/-- Norm formula for the scalar/transverse split. -/
theorem euclideanEightToRealProdSeven_norm_sq (s : ℝ) (y : E₇) :
    ‖(euclideanEightToRealProdSeven.symm (s, y) : E₈)‖ ^ 2 = s ^ 2 + ‖y‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp [euclideanEightToRealProdSeven, MeasurableEquiv.prodCongr, Fin.sum_univ_succ]

theorem euclideanEightToRealProdSeven_norm (s : ℝ) (y : E₇) :
    ‖(euclideanEightToRealProdSeven.symm (s, y) : E₈)‖ =
      Real.sqrt (s ^ 2 + ‖y‖ ^ 2) := by
  have hsq := euclideanEightToRealProdSeven_norm_sq s y
  have hnorm : 0 ≤ ‖(euclideanEightToRealProdSeven.symm (s, y) : E₈)‖ := norm_nonneg _
  have hsqrt : 0 ≤ Real.sqrt (s ^ 2 + ‖y‖ ^ 2) := Real.sqrt_nonneg _
  nlinarith [Real.sq_sqrt (show 0 ≤ s ^ 2 + ‖y‖ ^ 2 by positivity)]

/-- The coordinate split preserves Euclidean product volume. -/
theorem euclideanEightToRealProdSeven_measurePreserving :
    MeasurePreserving euclideanEightToRealProdSeven
      (volume : Measure E₈) ((volume : Measure ℝ).prod (volume : Measure E₇)) := by
  dsimp [euclideanEightToRealProdSeven]
  exact (PiLp.volume_preserving_ofLp (ι := Fin 8)).trans <|
    (volume_preserving_piFinSuccAbove (fun _ : Fin 8 => ℝ) 0).trans <| 
      MeasurePreserving.prod (MeasurePreserving.id volume)
        (PiLp.volume_preserving_toLp (Fin 7))

theorem integral_euclideanEight_eq_integral_realProdSeven (f : E₈ → ℝ) :
    (∫ x, f x ∂(volume : Measure E₈)) =
      ∫ p : ℝ × E₇, f (euclideanEightToRealProdSeven.symm p)
        ∂((volume : Measure ℝ).prod (volume : Measure E₇)) := by
  symm
  exact euclideanEightToRealProdSeven_measurePreserving.symm.integral_comp
    (MeasurableEquiv.measurableEmbedding euclideanEightToRealProdSeven.symm) f

/-- A compactly supported Cartesian test whose radial-polar angular factor is
`exp (κ u₀)`. -/
def eightDAxialCartesianTest (κ : ℝ) (x : E₈) : ℝ :=
  if hx : x = 0 then 0
  else if ‖x‖ < 1 then Real.exp (κ * (x 0 / ‖x‖)) else 0

/-- Scalar/transverse expression of the Cartesian test. -/
def eightDAxialPlaneSlice (κ s ρ : ℝ) : ℝ :=
  if s = 0 ∧ ρ = 0 then 0
  else if Real.sqrt (s ^ 2 + ρ ^ 2) < 1 then
    Real.exp (κ * (s / Real.sqrt (s ^ 2 + ρ ^ 2)))
  else 0

theorem eightDAxialCartesianTest_eq_planeSlice (κ s : ℝ) (y : E₇) :
    eightDAxialCartesianTest κ (euclideanEightToRealProdSeven.symm (s, y)) =
      eightDAxialPlaneSlice κ s ‖y‖ := by
  have hcoord := euclideanEightToRealProdSeven_symm_apply_zero s y
  have hnorm := euclideanEightToRealProdSeven_norm s y
  by_cases hs : s = 0 ∧ ‖y‖ = 0
  · have hx0 : euclideanEightToRealProdSeven.symm (s, y) = 0 := by
      apply norm_eq_zero.mp
      rw [hnorm]
      simp [hs]
    rw [eightDAxialCartesianTest, dif_pos hx0, eightDAxialPlaneSlice]
    simp [hs]
  · have hx : euclideanEightToRealProdSeven.symm (s, y) ≠ 0 := by
      intro h
      have hs0 : s = 0 := by
        have this := congrArg (fun x : E₈ => x 0) h
        rw [hcoord] at this
        exact this
      have hnorm0 : ‖euclideanEightToRealProdSeven.symm (s, y)‖ = 0 := by
        rw [h]
        simp
      rw [hnorm] at hnorm0
      have hsum : s ^ 2 + ‖y‖ ^ 2 = 0 := by
        nlinarith [Real.sq_sqrt (show 0 ≤ s ^ 2 + ‖y‖ ^ 2 by positivity)]
      have hy0 : ‖y‖ = 0 := by
        nlinarith [sq_nonneg s, sq_nonneg ‖y‖, norm_nonneg y, hsum]
      exact hs ⟨hs0, hy0⟩
    rw [eightDAxialCartesianTest, dif_neg hx, eightDAxialPlaneSlice, if_neg hs]
    rw [hnorm, hcoord]

theorem eightDAxialCartesianTest_integral_eq_planeSlice (κ : ℝ) :
    (∫ x : E₈, eightDAxialCartesianTest κ x ∂(volume : Measure E₈)) =
      ∫ p : ℝ × E₇, eightDAxialPlaneSlice κ p.1 ‖p.2‖
        ∂((volume : Measure ℝ).prod (volume : Measure E₇)) := by
  rw [integral_euclideanEight_eq_integral_realProdSeven]
  apply integral_congr_ae
  filter_upwards with p
  exact eightDAxialCartesianTest_eq_planeSlice κ p.1 p.2

def eightDAxialPlaneIntegrand (κ : ℝ) (p : ℝ × E₇) : ℝ :=
  eightDAxialPlaneSlice κ p.1 ‖p.2‖

theorem measurable_eightDAxialPlaneIntegrand (κ : ℝ) :
    Measurable (eightDAxialPlaneIntegrand κ) := by
  unfold eightDAxialPlaneIntegrand eightDAxialPlaneSlice
  refine Measurable.ite (by measurability) measurable_const ?_
  refine Measurable.ite (by measurability) ?_ measurable_const
  fun_prop

theorem eightDAxialPlaneIntegrand_norm_le (κ : ℝ) (p : ℝ × E₇) :
    ‖eightDAxialPlaneIntegrand κ p‖ ≤ Real.exp |κ| := by
  dsimp [eightDAxialPlaneIntegrand, eightDAxialPlaneSlice]
  by_cases hzero : p.1 = 0 ∧ ‖p.2‖ = 0
  · simp [hzero]
    positivity
  · by_cases hball : Real.sqrt (p.1 ^ 2 + ‖p.2‖ ^ 2) < 1
    · have hsum : 0 < p.1 ^ 2 + ‖p.2‖ ^ 2 := by
        by_contra h
        have heq : p.1 ^ 2 + ‖p.2‖ ^ 2 = 0 :=
          le_antisymm (le_of_not_gt h) (by positivity)
        have hs : p.1 = 0 := by nlinarith [sq_nonneg p.1, sq_nonneg ‖p.2‖]
        have hy : ‖p.2‖ = 0 := by nlinarith [sq_nonneg p.1, sq_nonneg ‖p.2‖]
        exact hzero ⟨hs, hy⟩
      have hd : 0 < Real.sqrt (p.1 ^ 2 + ‖p.2‖ ^ 2) := Real.sqrt_pos.2 hsum
      have hratio : |p.1 / Real.sqrt (p.1 ^ 2 + ‖p.2‖ ^ 2)| ≤ 1 := by
        rw [abs_div, abs_of_pos hd]
        apply (div_le_one hd).2
        exact Real.abs_le_sqrt (by nlinarith [sq_nonneg ‖p.2‖])
      have hprod : κ * (p.1 / Real.sqrt (p.1 ^ 2 + ‖p.2‖ ^ 2)) ≤ |κ| := by
        calc
          κ * (p.1 / Real.sqrt (p.1 ^ 2 + ‖p.2‖ ^ 2)) ≤
              |κ * (p.1 / Real.sqrt (p.1 ^ 2 + ‖p.2‖ ^ 2))| := le_abs_self _
          _ = |κ| * |p.1 / Real.sqrt (p.1 ^ 2 + ‖p.2‖ ^ 2)| := abs_mul _ _
          _ ≤ |κ| := by nlinarith [abs_nonneg κ, hratio]
      rw [if_neg hzero, if_pos hball, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr hprod
    · simp [hzero, hball]
      positivity

theorem integrable_eightDAxialPlaneIntegrand (κ : ℝ) :
    Integrable (eightDAxialPlaneIntegrand κ)
      ((volume : Measure ℝ).prod (volume : Measure E₇)) := by
  let rect : Set (ℝ × E₇) := Icc (-1 : ℝ) 1 ×ˢ Metric.closedBall (0 : E₇) 1
  have hcompact : IsCompact rect := by
    dsimp [rect]
    exact isCompact_Icc.prod (isCompact_closedBall 0 1)
  have hfinite : ((volume : Measure ℝ).prod (volume : Measure E₇)) rect ≠ ⊤ :=
    hcompact.measure_ne_top
  have hmeas := measurable_eightDAxialPlaneIntegrand κ
  have hbound : ∀ᵐ p ∂(((volume : Measure ℝ).prod (volume : Measure E₇)).restrict rect),
      ‖eightDAxialPlaneIntegrand κ p‖ ≤ Real.exp |κ| :=
    Filter.Eventually.of_forall fun p => eightDAxialPlaneIntegrand_norm_le κ p
  have hion : IntegrableOn (eightDAxialPlaneIntegrand κ) rect
      ((volume : Measure ℝ).prod (volume : Measure E₇)) :=
    Measure.integrableOn_of_bounded hfinite hmeas.aestronglyMeasurable hbound
  have hzero_outside : ∀ p, p ∉ rect → eightDAxialPlaneIntegrand κ p = 0 := by
    rintro ⟨s, y⟩ hp
    by_contra hne
    have hball : Real.sqrt (s ^ 2 + ‖y‖ ^ 2) < 1 := by
      by_contra hb
      by_cases hz : s = 0 ∧ ‖y‖ = 0
      · simp [eightDAxialPlaneIntegrand, eightDAxialPlaneSlice, hz] at hne
      · simp [eightDAxialPlaneIntegrand, eightDAxialPlaneSlice, hz, hb] at hne
    have hsabs : |s| ≤ Real.sqrt (s ^ 2 + ‖y‖ ^ 2) :=
      Real.abs_le_sqrt (by nlinarith [sq_nonneg ‖y‖])
    have hybound : ‖y‖ ≤ Real.sqrt (s ^ 2 + ‖y‖ ^ 2) :=
      Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg s])
    have hslo : -1 ≤ s := by nlinarith [abs_le.mp hsabs]
    have hshi : s ≤ 1 := by nlinarith [abs_le.mp hsabs]
    have hymem : y ∈ Metric.closedBall (0 : E₇) 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      nlinarith
    exact hp ⟨⟨hslo, hshi⟩, hymem⟩
  exact hion.integrable_of_forall_notMem_eq_zero hzero_outside

/-- The planar half-space integrand after integrating out the S⁴ directions. -/
def eightDAxialPlaneWeightedIntegrand (κ : ℝ) (p : ℝ × ℝ) : ℝ :=
  (16 * Real.pi ^ 3 / 15) * p.2 ^ 6 * eightDAxialPlaneSlice κ p.1 p.2

private def eightDAxialPositiveHalfPlaneIntegrand
    (F : ℝ × ℝ → ℝ) (z : ℂ) : ℝ :=
  if 0 < z.im then F (z.re, z.im) else 0

/-- Polar evaluation of the scalar/transverse slice. -/
theorem eightDAxialPlaneSlice_polar_eq
    (κ r θ : ℝ) (hr : 0 < r) (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    eightDAxialPlaneSlice κ (r * Real.cos θ) (r * Real.sin θ) =
      if r < 1 then Real.exp (κ * Real.cos θ) else 0 := by
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ hθπ
  have hrho : 0 < r * Real.sin θ := mul_pos hr hsin
  have hsum : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
    calc
      (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 =
          r ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
      _ = r ^ 2 := by rw [Real.cos_sq_add_sin_sq]; ring
  have hrad : Real.sqrt ((r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2) = r := by
    rw [hsum, Real.sqrt_sq_eq_abs, abs_of_pos hr]
  have hzero : ¬(r * Real.cos θ = 0 ∧ r * Real.sin θ = 0) := by
    rintro ⟨_, h⟩
    exact (ne_of_gt hrho) h
  by_cases hcut : r < 1
  · have hd : r ≠ 0 := ne_of_gt hr
    have hratio : r * Real.cos θ / r = Real.cos θ := by field_simp [hd]
    simp only [eightDAxialPlaneSlice, if_neg hzero, if_pos hcut, hrad, hratio]
  · simp only [eightDAxialPlaneSlice, if_neg hzero, if_neg hcut, hrad]

theorem polarCoord_symm_re_eightD (r θ : ℝ) :
    (Complex.polarCoord.symm (r, θ)).re = r * Real.cos θ := by
  rw [Complex.polarCoord_symm_apply]
  simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im,
    zero_mul, mul_zero, zero_add, one_mul, sub_zero]
  ring

theorem polarCoord_symm_im_eightD (r θ : ℝ) :
    (Complex.polarCoord.symm (r, θ)).im = r * Real.sin θ := by
  rw [Complex.polarCoord_symm_apply]
  simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im,
    zero_mul, mul_zero, zero_add, one_mul]
  ring

theorem eightDSin_pos_iff_angle_pos (θ : ℝ) (hlo : -Real.pi < θ)
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

theorem polarCoord_symm_im_pos_iff_eightD (r θ : ℝ) (hr : 0 < r)
    (hlo : -Real.pi < θ) (hhi : θ < Real.pi) :
    0 < (Complex.polarCoord.symm (r, θ)).im ↔ 0 < θ ∧ θ < Real.pi := by
  rw [polarCoord_symm_im_eightD, mul_pos_iff_of_pos_left hr]
  exact eightDSin_pos_iff_angle_pos θ hlo hhi

/-- The half-plane extension becomes the angle rectangle integrand under the
actual Mathlib complex polar-coordinate Jacobian. -/
theorem eightDAxialPlaneWeightedIntegrand_polar_eq
    (κ r θ : ℝ) (hr : 0 < r) (hlo : -Real.pi < θ) (hhi : θ < Real.pi) :
    r * eightDAxialPositiveHalfPlaneIntegrand
        (eightDAxialPlaneWeightedIntegrand κ) (Complex.polarCoord.symm (r, θ)) =
      if 0 < θ ∧ θ < Real.pi then
        if r < 1 then
          (16 * Real.pi ^ 3 / 15) * r ^ 7 * Real.sin θ ^ 6 *
            Real.exp (κ * Real.cos θ)
        else 0
      else 0 := by
  let z : ℂ := Complex.polarCoord.symm (r, θ)
  have hre : z.re = r * Real.cos θ := polarCoord_symm_re_eightD r θ
  have him : z.im = r * Real.sin θ := polarCoord_symm_im_eightD r θ
  by_cases hθ : 0 < θ ∧ θ < Real.pi
  · have hzpos : 0 < z.im := by
      rw [him]
      exact mul_pos hr (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)
    change r * (if 0 < z.im then
      eightDAxialPlaneWeightedIntegrand κ (z.re, z.im) else 0) = _
    rw [if_pos hzpos]
    simp only [eightDAxialPlaneWeightedIntegrand]
    rw [hre, him, eightDAxialPlaneSlice_polar_eq κ r θ hr hθ.1 hθ.2]
    by_cases hc : r < 1 <;> simp [hc, hθ] <;> ring
  · have hznot : ¬ 0 < z.im := by
      intro hz
      exact hθ ((polarCoord_symm_im_pos_iff_eightD r θ hr hlo hhi).1 hz)
    change r * (if 0 < z.im then
      eightDAxialPlaneWeightedIntegrand κ (z.re, z.im) else 0) = _
    simp [hznot, hθ]

private def eightDAxialAngleChartIntegrand (κ : ℝ) (p : ℝ × ℝ) : ℝ :=
  if 0 < p.2 ∧ p.2 < Real.pi then
    if p.1 < 1 then
      (16 * Real.pi ^ 3 / 15) * p.1 ^ 7 * Real.sin p.2 ^ 6 *
        Real.exp (κ * Real.cos p.2)
    else 0
  else 0

private def eightDAxialAngleRectangleIntegrand (κ : ℝ) (p : ℝ × ℝ) : ℝ :=
  (16 * Real.pi ^ 3 / 15) * p.1 ^ 7 * Real.sin p.2 ^ 6 *
    Real.exp (κ * Real.cos p.2)

private theorem eightDAxialAngleRectangleIntegrand_continuous (κ : ℝ) :
    Continuous (eightDAxialAngleRectangleIntegrand κ) := by
  unfold eightDAxialAngleRectangleIntegrand
  fun_prop

private theorem eightDAxialAngleRectangleIntegrand_integrableOn
    (κ : ℝ) :
    IntegrableOn (eightDAxialAngleRectangleIntegrand κ)
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) Real.pi)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
  let K : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) Real.pi
  have hcompact : IsCompact K := by
    dsimp [K]
    exact isCompact_Icc.prod isCompact_Icc
  have hsubset : Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) Real.pi ⊆ K := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    simp only [K, mem_prod, mem_Icc]
    exact ⟨⟨le_of_lt hr.1, le_of_lt hr.2⟩,
      ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩⟩
  have hcont : ContinuousOn (eightDAxialAngleRectangleIntegrand κ) K :=
    (eightDAxialAngleRectangleIntegrand_continuous κ).continuousOn
  exact hcont.integrableOn_of_subset_isCompact hcompact
    (measurableSet_Ioo.prod measurableSet_Ioo) hsubset
    (ne_top_of_le_ne_top hcompact.measure_ne_top (measure_mono hsubset))

/-- The `toSphere` half-plane chart and the compact radius-angle rectangle
have exactly the same indicator integrand. -/
private theorem eightDAxialAngleChart_eq_rectangle (κ : ℝ) :
    (∫ p in Complex.polarCoord.target, eightDAxialAngleChartIntegrand κ p) =
      ∫ r in Ioo (0 : ℝ) 1, ∫ θ in Ioo (0 : ℝ) Real.pi,
        eightDAxialAngleRectangleIntegrand κ (r, θ) := by
  let target : Set (ℝ × ℝ) := Complex.polarCoord.target
  let rect : Set (ℝ × ℝ) := Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) Real.pi
  have htarget : MeasurableSet target := Complex.polarCoord.open_target.measurableSet
  have hrect : MeasurableSet rect := measurableSet_Ioo.prod measurableSet_Ioo
  have hindicator : target.indicator (eightDAxialAngleChartIntegrand κ) =
      rect.indicator (eightDAxialAngleRectangleIntegrand κ) := by
    classical
    funext p
    rcases p with ⟨r, θ⟩
    by_cases hr0 : 0 < r
    · by_cases hr1 : r < 1
      · by_cases ht0 : 0 < θ
        · by_cases htpi : θ < Real.pi
          · have htlo : -Real.pi < θ := by linarith [Real.pi_pos]
            simp [Set.indicator_apply, eightDAxialAngleChartIntegrand,
              eightDAxialAngleRectangleIntegrand, target, rect,
              Complex.polarCoord_target, mem_prod, mem_Ioi, mem_Ioo,
              hr0, hr1, ht0, htpi, htlo]
          · simp [Set.indicator_apply, eightDAxialAngleChartIntegrand,
              eightDAxialAngleRectangleIntegrand, target, rect,
              Complex.polarCoord_target, mem_prod, mem_Ioi, mem_Ioo,
              hr0, hr1, ht0, htpi]
        · simp [Set.indicator_apply, eightDAxialAngleChartIntegrand,
            eightDAxialAngleRectangleIntegrand, target, rect,
            Complex.polarCoord_target, mem_prod, mem_Ioi, mem_Ioo,
            hr0, hr1, ht0]
      · simp [Set.indicator_apply, eightDAxialAngleChartIntegrand,
          eightDAxialAngleRectangleIntegrand, target, rect,
          Complex.polarCoord_target, mem_prod, mem_Ioi, mem_Ioo,
          hr0, hr1]
    · simp [Set.indicator_apply, eightDAxialAngleChartIntegrand,
        eightDAxialAngleRectangleIntegrand, target, rect,
        Complex.polarCoord_target, mem_prod, mem_Ioi, mem_Ioo, hr0]
  calc
    _ = ∫ p, target.indicator (eightDAxialAngleChartIntegrand κ) p := by
      rw [← integral_indicator htarget]
    _ = ∫ p, rect.indicator (eightDAxialAngleRectangleIntegrand κ) p := by
      rw [hindicator]
    _ = ∫ p in rect, eightDAxialAngleRectangleIntegrand κ p := by
      rw [integral_indicator hrect]
    _ = ∫ r in Ioo (0 : ℝ) 1, ∫ θ in Ioo (0 : ℝ) Real.pi,
          eightDAxialAngleRectangleIntegrand κ (r, θ) :=
      setIntegral_prod (eightDAxialAngleRectangleIntegrand κ)
        (eightDAxialAngleRectangleIntegrand_integrableOn κ)

/-- Actual complex-polar change of variables for the eight-dimensional angular
test, before evaluating the bounded rectangle integral. -/
private theorem integral_eightDAxialPlaneWeightedComplex_eq_chart (κ : ℝ) :
    (∫ z, eightDAxialPositiveHalfPlaneIntegrand
      (eightDAxialPlaneWeightedIntegrand κ) z) =
      ∫ p in Complex.polarCoord.target, eightDAxialAngleChartIntegrand κ p := by
  rw [← Complex.integral_comp_polarCoord_symm
    (eightDAxialPositiveHalfPlaneIntegrand (eightDAxialPlaneWeightedIntegrand κ))]
  apply setIntegral_congr_fun Complex.polarCoord.open_target.measurableSet
  intro p hp
  have hp' : 0 < p.1 ∧ -Real.pi < p.2 ∧ p.2 < Real.pi := by
    simpa only [Complex.polarCoord_target, mem_prod, mem_Ioi, mem_Ioo] using hp
  have hpoint := eightDAxialPlaneWeightedIntegrand_polar_eq
    κ p.1 p.2 hp'.1 hp'.2.1 hp'.2.2
  simpa only [smul_eq_mul, eightDAxialAngleChartIntegrand] using hpoint

private def eightDAxialAngleFactor (κ θ : ℝ) : ℝ :=
  Real.sin θ ^ 6 * Real.exp (κ * Real.cos θ)

private theorem integral_Ioo_fifth_power :
    (∫ r in Ioo (0 : ℝ) 1, r ^ 7) = (1 / 8 : ℝ) := by
  calc
    _ = ∫ r in Ioc (0 : ℝ) 1, r ^ 7 := by
      rw [← integral_Ioc_eq_integral_Ioo]
    _ = ∫ r in (0 : ℝ)..1, r ^ 7 := by
      rw [← intervalIntegral.integral_of_le (by norm_num)]
    _ = (1 / 8 : ℝ) := by
      rw [integral_pow]
      norm_num

private theorem integral_eightDAxialAngleFactor_Ioo_eq_interval (κ : ℝ) :
    (∫ θ in Ioo (0 : ℝ) Real.pi, eightDAxialAngleFactor κ θ) =
      ∫ θ in (0 : ℝ)..Real.pi, eightDAxialAngleFactor κ θ := by
  calc
    _ = ∫ θ in Ioc (0 : ℝ) Real.pi, eightDAxialAngleFactor κ θ := by
      rw [← integral_Ioc_eq_integral_Ioo]
    _ = ∫ θ in (0 : ℝ)..Real.pi, eightDAxialAngleFactor κ θ := by
      rw [← intervalIntegral.integral_of_le (le_of_lt Real.pi_pos)]

private theorem integral_eightDAxialAngleRectangle_eq_interval (κ : ℝ) :
    (∫ r in Ioo (0 : ℝ) 1, ∫ θ in Ioo (0 : ℝ) Real.pi,
      eightDAxialAngleRectangleIntegrand κ (r, θ)) =
      (16 * Real.pi ^ 3 / 120) *
        ∫ θ in (0 : ℝ)..Real.pi, eightDAxialAngleFactor κ θ := by
  calc
    _ = ∫ r in Ioo (0 : ℝ) 1,
        ((16 * Real.pi ^ 3 / 15) * r ^ 7) *
          (∫ θ in Ioo (0 : ℝ) Real.pi, eightDAxialAngleFactor κ θ) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro r hr
      calc
        _ = ∫ θ in Ioo (0 : ℝ) Real.pi,
            ((16 * Real.pi ^ 3 / 15) * r ^ 7) * eightDAxialAngleFactor κ θ := by
          apply setIntegral_congr_fun measurableSet_Ioo
          intro θ hθ
          simp [eightDAxialAngleRectangleIntegrand, eightDAxialAngleFactor]
          ring
        _ = _ := by rw [integral_const_mul]
    _ = (∫ θ in Ioo (0 : ℝ) Real.pi, eightDAxialAngleFactor κ θ) *
        ((16 * Real.pi ^ 3 / 15) * ∫ r in Ioo (0 : ℝ) 1, r ^ 7) := by
      calc
        _ = ∫ r in Ioo (0 : ℝ) 1,
            (∫ θ in Ioo (0 : ℝ) Real.pi, eightDAxialAngleFactor κ θ) *
              ((16 * Real.pi ^ 3 / 15) * r ^ 7) := by
          apply setIntegral_congr_fun measurableSet_Ioo
          intro r hr
          ring
        _ = (∫ θ in Ioo (0 : ℝ) Real.pi, eightDAxialAngleFactor κ θ) *
            (∫ r in Ioo (0 : ℝ) 1, (16 * Real.pi ^ 3 / 15) * r ^ 7) := by
          rw [integral_const_mul]
        _ = _ := by rw [integral_const_mul]
    _ = (16 * Real.pi ^ 3 / 120) *
        ∫ θ in (0 : ℝ)..Real.pi, eightDAxialAngleFactor κ θ := by
      rw [integral_Ioo_fifth_power, integral_eightDAxialAngleFactor_Ioo_eq_interval]
      ring

private theorem integral_eightDAxialPlaneWeightedComplex_eq_angle (κ : ℝ) :
    (∫ z, eightDAxialPositiveHalfPlaneIntegrand
      (eightDAxialPlaneWeightedIntegrand κ) z) =
      (16 * Real.pi ^ 3 / 120) *
        ∫ θ in (0 : ℝ)..Real.pi, eightDAxialAngleFactor κ θ := by
  calc
    _ = ∫ p in Complex.polarCoord.target, eightDAxialAngleChartIntegrand κ p :=
      integral_eightDAxialPlaneWeightedComplex_eq_chart κ
    _ = ∫ r in Ioo (0 : ℝ) 1, ∫ θ in Ioo (0 : ℝ) Real.pi,
          eightDAxialAngleRectangleIntegrand κ (r, θ) :=
      eightDAxialAngleChart_eq_rectangle κ
    _ = (16 * Real.pi ^ 3 / 120) *
          ∫ θ in (0 : ℝ)..Real.pi, eightDAxialAngleFactor κ θ :=
      integral_eightDAxialAngleRectangle_eq_interval κ

/-- Unit radial cutoff for the E6 polar comparison. -/
def eightDAxialRadialCutoff (r : Ioi (0 : ℝ)) : ℝ :=
  (Iio (⟨1, mem_Ioi.mpr one_pos⟩ : Ioi (0 : ℝ))).indicator (fun _ => 1) r

theorem eightDAxialRadialCutoff_integral :
    (∫ r : Ioi (0 : ℝ), eightDAxialRadialCutoff r
      ∂(Measure.volumeIoiPow 7)) = (1 / 8 : ℝ) := by
  calc
    _ = (Measure.volumeIoiPow 7).real
        (Iio (⟨1, mem_Ioi.mpr one_pos⟩ : Ioi (0 : ℝ))) :=
      integral_indicator_one measurableSet_Iio
    _ = (1 / 8 : ℝ) := by
      norm_num [Measure.real, Measure.volumeIoiPow_apply_Iio]

theorem eightDAxialCartesianTest_smul_factor
    (κ : ℝ) (u : S₈) (r : Ioi (0 : ℝ)) :
    eightDAxialCartesianTest κ ((r : ℝ) • (u : E₈)) =
      Real.exp (κ * (u : E₈) 0) * eightDAxialRadialCutoff r := by
  have hr : 0 < (r : ℝ) := r.2
  have hu : ‖(u : E₈)‖ = 1 := by simpa [dist_eq_norm] using u.2
  have hnorm : ‖(r : ℝ) • (u : E₈)‖ = (r : ℝ) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hu, mul_one]
  have hne : (r : ℝ) • (u : E₈) ≠ 0 := by
    intro hz
    have hz' : ‖(r : ℝ) • (u : E₈)‖ = 0 := by simpa using congrArg norm hz
    rw [hnorm] at hz'
    linarith
  have hcoord : ((r : ℝ) • (u : E₈)) 0 / ‖(r : ℝ) • (u : E₈)‖ = (u : E₈) 0 := by
    rw [hnorm]
    change ((r : ℝ) * (u : E₈).ofLp 0) / (r : ℝ) = (u : E₈).ofLp 0
    field_simp [ne_of_gt hr]
  by_cases hr1 : (r : ℝ) < 1
  · have hlt : ‖(r : ℝ) • (u : E₈)‖ < 1 := by simpa [hnorm] using hr1
    have hcut : r ∈ Iio (⟨1, mem_Ioi.mpr one_pos⟩ : Ioi (0 : ℝ)) := by
      change (r : ℝ) < 1
      exact hr1
    simp only [eightDAxialCartesianTest, dif_neg hne, if_pos hlt]
    rw [hcoord]
    change Real.exp (κ * (u : E₈) 0) = Real.exp (κ * (u : E₈) 0) *
      (Iio (⟨1, mem_Ioi.mpr one_pos⟩ : Ioi (0 : ℝ))).indicator (fun _ => 1) r
    rw [Set.indicator_of_mem hcut]
    simp
  · have hnotlt : ¬‖(r : ℝ) • (u : E₈)‖ < 1 := by simpa [hnorm] using hr1
    have hcut : r ∉ Iio (⟨1, mem_Ioi.mpr one_pos⟩ : Ioi (0 : ℝ)) := by
      change ¬(r : ℝ) < 1
      exact hr1
    simp only [eightDAxialCartesianTest, dif_neg hne, if_neg hnotlt]
    change (0 : ℝ) = Real.exp (κ * (u : E₈) 0) *
      (Iio (⟨1, mem_Ioi.mpr one_pos⟩ : Ioi (0 : ℝ))).indicator (fun _ => 1) r
    rw [Set.indicator_of_notMem hcut]
    simp

theorem eightDAxialCartesianTest_integral_factor (κ : ℝ) :
    (∫ x : E₈, eightDAxialCartesianTest κ x ∂(volume : Measure E₈)) =
      (∫ u : S₈, Real.exp (κ * (u : E₈) 0)
        ∂((volume : Measure E₈).toSphere)) *
        ∫ r : Ioi (0 : ℝ), eightDAxialRadialCutoff r
          ∂(Measure.volumeIoiPow (Module.finrank ℝ E₈ - 1)) := by
  rw [integral_euclidean_polarProduct (f := eightDAxialCartesianTest κ)]
  simp only [show Module.finrank ℝ E₈ - 1 = 7 by simp]
  calc
    (∫ p : S₈ × Ioi (0 : ℝ),
        eightDAxialCartesianTest κ ((p.2 : ℝ) • (p.1 : E₈)) ∂
          ((volume : Measure E₈).toSphere.prod (Measure.volumeIoiPow 7))) =
        ∫ p : S₈ × Ioi (0 : ℝ),
          Real.exp (κ * (p.1 : E₈) 0) * eightDAxialRadialCutoff p.2 ∂
            ((volume : Measure E₈).toSphere.prod (Measure.volumeIoiPow 7)) := by
      apply integral_congr_ae
      filter_upwards with p
      exact eightDAxialCartesianTest_smul_factor κ p.1 p.2
    _ = (∫ u : S₈, Real.exp (κ * (u : E₈) 0)
          ∂((volume : Measure E₈).toSphere)) *
        ∫ r : Ioi (0 : ℝ), eightDAxialRadialCutoff r
          ∂(Measure.volumeIoiPow 7) :=
      integral_prod_mul (fun u : S₈ => Real.exp (κ * (u : E₈) 0))
        eightDAxialRadialCutoff

/-- Expose the fourth-power radial measure as a Lebesgue integral on the
positive subtype. -/
private theorem integral_volumeIoiPow_four_eq_Ioi
    (f : Ioi (0 : ℝ) → ℝ) :
    (∫ r, f r ∂(Measure.volumeIoiPow 6)) =
      ∫ r : Ioi (0 : ℝ), (r : ℝ) ^ 6 * f r
        ∂(Measure.comap Subtype.val (volume : Measure ℝ)) := by
  rw [Measure.volumeIoiPow, integral_withDensity_eq_integral_toReal_smul]
  · congr 1
    funext r
    simp only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (r : ℝ) ^ 6)]
    simp [smul_eq_mul]
  · fun_prop
  · filter_upwards with r
    simp

private def eightDAxialPositiveSubtypeIntegrand (κ : ℝ) (p : ℝ × Ioi (0 : ℝ)) : ℝ :=
  (16 * Real.pi ^ 3 / 15) * (p.2 : ℝ) ^ 6 * eightDAxialPlaneSlice κ p.1 p.2

private def eightDAxialPlaneAmbientIntegrand (κ : ℝ) (p : ℝ × ℝ) : ℝ :=
  if 0 < p.2 then eightDAxialPlaneWeightedIntegrand κ p else 0

private theorem measurable_eightDAxialPlaneAmbientIntegrand (κ : ℝ) :
    Measurable (eightDAxialPlaneAmbientIntegrand κ) := by
  have hslice : Measurable (fun p : ℝ × ℝ => eightDAxialPlaneSlice κ p.1 p.2) := by
    unfold eightDAxialPlaneSlice
    refine Measurable.ite (by measurability) measurable_const ?_
    refine Measurable.ite (by measurability) ?_ measurable_const
    fun_prop
  unfold eightDAxialPlaneAmbientIntegrand eightDAxialPlaneWeightedIntegrand
  refine Measurable.ite (by measurability) ?_ measurable_const
  exact (measurable_const.mul (measurable_snd.pow_const _)).mul hslice

private theorem eightDAxialPlaneAmbientIntegrand_norm_le (κ : ℝ)
    (p : ℝ × ℝ) :
    ‖eightDAxialPlaneAmbientIntegrand κ p‖ ≤
      (16 * Real.pi ^ 3 / 15) * Real.exp |κ| := by
  by_cases hy : 0 < p.2
  · by_cases hz : eightDAxialPlaneSlice κ p.1 p.2 = 0
    · simp [eightDAxialPlaneAmbientIntegrand, eightDAxialPlaneWeightedIntegrand, hy, hz]
      positivity
    · have hcut : Real.sqrt (p.1 ^ 2 + p.2 ^ 2) < 1 := by
        by_contra hc
        simp [eightDAxialPlaneSlice, hc] at hz
      have hbase : ‖eightDAxialPlaneSlice κ p.1 p.2‖ ≤ Real.exp |κ| := by
        have hzero : ¬(p.1 = 0 ∧ p.2 = 0) := by
          rintro ⟨_, hr⟩
          exact (ne_of_gt hy) hr
        have hsum : 0 < p.1 ^ 2 + p.2 ^ 2 := by positivity
        have hd : 0 < Real.sqrt (p.1 ^ 2 + p.2 ^ 2) := Real.sqrt_pos.2 hsum
        have hratio : |p.1 / Real.sqrt (p.1 ^ 2 + p.2 ^ 2)| ≤ 1 := by
          rw [abs_div, abs_of_pos hd]
          apply (div_le_one hd).2
          exact Real.abs_le_sqrt (by nlinarith [sq_nonneg p.2])
        have hprod : κ * (p.1 / Real.sqrt (p.1 ^ 2 + p.2 ^ 2)) ≤ |κ| := by
          calc
            κ * (p.1 / Real.sqrt (p.1 ^ 2 + p.2 ^ 2)) ≤
                |κ * (p.1 / Real.sqrt (p.1 ^ 2 + p.2 ^ 2))| := le_abs_self _
            _ = |κ| * |p.1 / Real.sqrt (p.1 ^ 2 + p.2 ^ 2)| := abs_mul _ _
            _ ≤ |κ| := by nlinarith [abs_nonneg κ, hratio]
        rw [eightDAxialPlaneSlice, if_neg hzero, if_pos hcut,
          Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr hprod
      have hsquare : p.2 ^ 2 ≤ 1 := by
        have hrad : p.2 ≤ Real.sqrt (p.1 ^ 2 + p.2 ^ 2) :=
          Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg p.1])
        have hsmall : p.2 < 1 := lt_of_le_of_lt hrad hcut
        nlinarith [sq_nonneg (p.2 - 1)]
      have hr : p.2 ^ 6 ≤ 1 := by nlinarith [sq_nonneg (p.2 ^ 2), hsquare]
      unfold eightDAxialPlaneAmbientIntegrand eightDAxialPlaneWeightedIntegrand
      rw [if_pos hy, Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg (by positivity : 0 ≤ (16 * Real.pi ^ 3 / 15 : ℝ)),
        abs_of_nonneg (by positivity : 0 ≤ p.2 ^ 6)]
      calc
        (16 * Real.pi ^ 3 / 15) * p.2 ^ 6 *
            ‖eightDAxialPlaneSlice κ p.1 p.2‖ ≤
          (16 * Real.pi ^ 3 / 15) * 1 * Real.exp |κ| := by
            gcongr
        _ = (16 * Real.pi ^ 3 / 15) * Real.exp |κ| := by ring
  · simp [eightDAxialPlaneAmbientIntegrand, hy]
    positivity

private theorem integrable_eightDAxialPlaneAmbientIntegrand (κ : ℝ) :
    Integrable (eightDAxialPlaneAmbientIntegrand κ)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
  let K : Set (ℝ × ℝ) := Icc (-1 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  have hcompact : IsCompact K := by
    dsimp [K]
    exact isCompact_Icc.prod isCompact_Icc
  have hfinite : ((volume : Measure ℝ).prod (volume : Measure ℝ)) K ≠ ⊤ :=
    hcompact.measure_ne_top
  have hmeas := measurable_eightDAxialPlaneAmbientIntegrand κ
  have hbound : ∀ᵐ p ∂(((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict K),
      ‖eightDAxialPlaneAmbientIntegrand κ p‖ ≤
        (16 * Real.pi ^ 3 / 15) * Real.exp |κ| :=
    Filter.Eventually.of_forall fun p => eightDAxialPlaneAmbientIntegrand_norm_le κ p
  have hion : IntegrableOn (eightDAxialPlaneAmbientIntegrand κ) K
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    Measure.integrableOn_of_bounded hfinite hmeas.aestronglyMeasurable hbound
  have hzero_outside : ∀ p, p ∉ K → eightDAxialPlaneAmbientIntegrand κ p = 0 := by
    rintro ⟨s, r⟩ hp
    by_contra hne
    have hr : 0 < r := by
      by_contra hn
      simp [eightDAxialPlaneAmbientIntegrand, hn] at hne
    have hcut : Real.sqrt (s ^ 2 + r ^ 2) < 1 := by
      by_contra hc
      have hz : ¬(s = 0 ∧ r = 0) := by rintro ⟨_, hr0⟩; linarith
      simp [eightDAxialPlaneAmbientIntegrand, eightDAxialPlaneWeightedIntegrand,
        eightDAxialPlaneSlice, hr, hz, hc] at hne
    have hsabs : |s| ≤ Real.sqrt (s ^ 2 + r ^ 2) :=
      Real.abs_le_sqrt (by nlinarith [sq_nonneg r])
    have hrbound : r ≤ Real.sqrt (s ^ 2 + r ^ 2) :=
      Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg s])
    have hmem : (s, r) ∈ K := by
      simp only [K, mem_prod, mem_Icc]
      exact ⟨⟨by nlinarith [abs_le.mp hsabs], by nlinarith [abs_le.mp hsabs]⟩,
        ⟨le_of_lt hr, by nlinarith⟩⟩
    exact hp hmem
  exact hion.integrable_of_forall_notMem_eq_zero hzero_outside

private theorem integrable_eightDAxialPositiveSubtypeIntegrand (κ : ℝ) :
    Integrable (eightDAxialPositiveSubtypeIntegrand κ)
      ((volume : Measure ℝ).prod
        (Measure.comap (Subtype.val : Ioi (0 : ℝ) → ℝ)
          (volume : Measure ℝ))) := by
  let e : MeasurableEmbedding
      (Prod.map (id : ℝ → ℝ) (Subtype.val : Ioi (0 : ℝ) → ℝ)) :=
    MeasurableEmbedding.id.prodMap
      (MeasurableEmbedding.subtype_coe measurableSet_Ioi)
  have hF : Integrable (eightDAxialPlaneAmbientIntegrand κ)
      (((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict
        (Set.univ ×ˢ Ioi (0 : ℝ))) :=
    (integrable_eightDAxialPlaneAmbientIntegrand κ).mono_measure Measure.restrict_le_self
  have hmap : Measure.map
      (Prod.map (id : ℝ → ℝ) (Subtype.val : Ioi (0 : ℝ) → ℝ))
      ((volume : Measure ℝ).prod
        (Measure.comap (Subtype.val : Ioi (0 : ℝ) → ℝ) (volume : Measure ℝ))) =
      ((volume : Measure ℝ).prod (volume : Measure ℝ)).restrict
        (Set.univ ×ˢ Ioi (0 : ℝ)) := map_product_volume_positiveSubtype
  have hcomp : Integrable
      (eightDAxialPlaneAmbientIntegrand κ ∘ fun p : ℝ × Ioi (0 : ℝ) =>
        (p.1, (p.2 : ℝ)))
      ((volume : Measure ℝ).prod
        (Measure.comap (Subtype.val : Ioi (0 : ℝ) → ℝ) (volume : Measure ℝ))) := by
    apply e.integrable_map_iff.mp
    rw [hmap]
    exact hF
  apply hcomp.congr
  filter_upwards with p
  change eightDAxialPlaneAmbientIntegrand κ (p.1, (p.2 : ℝ)) =
    eightDAxialPositiveSubtypeIntegrand κ p
  unfold eightDAxialPlaneAmbientIntegrand eightDAxialPositiveSubtypeIntegrand
    eightDAxialPlaneWeightedIntegrand
  change (if 0 < (p.2 : ℝ) then
      (16 * Real.pi ^ 3 / 15) * (p.2 : ℝ) ^ 6 *
        eightDAxialPlaneSlice κ p.1 (p.2 : ℝ) else 0) = _
  have hp : 0 < (p.2 : ℝ) := p.2.2
  simp [hp]

private theorem integral_eightDAxial_scalarRadial_eq_positiveHalfPlane (κ : ℝ) :
    (∫ s : ℝ, (16 * Real.pi ^ 3 / 15) *
      ∫ r : Ioi (0 : ℝ), eightDAxialPlaneSlice κ s r
        ∂(Measure.volumeIoiPow 6) ∂(volume : Measure ℝ)) =
      ∫ z, eightDAxialPositiveHalfPlaneIntegrand
        (eightDAxialPlaneWeightedIntegrand κ) z := by
  have hsubtype :
      (∫ s : ℝ, (16 * Real.pi ^ 3 / 15) *
        ∫ r : Ioi (0 : ℝ), eightDAxialPlaneSlice κ s r
          ∂(Measure.volumeIoiPow 6) ∂(volume : Measure ℝ)) =
      ∫ s : ℝ, ∫ r : Ioi (0 : ℝ), eightDAxialPositiveSubtypeIntegrand κ (s, r)
          ∂(Measure.comap Subtype.val (volume : Measure ℝ)) ∂(volume : Measure ℝ) := by
    apply integral_congr_ae
    filter_upwards with s
    rw [integral_volumeIoiPow_four_eq_Ioi]
    rw [← integral_const_mul]
    congr 1
    funext r
    dsimp [eightDAxialPositiveSubtypeIntegrand]
    ring_nf
  rw [hsubtype]
  letI : SigmaFinite
      (Measure.comap (Subtype.val : Ioi (0 : ℝ) → ℝ) (volume : Measure ℝ)) :=
      SigmaFinite.of_map _ measurable_subtype_coe.aemeasurable (by
        rw [map_comap_subtype_coe measurableSet_Ioi]
        infer_instance)
  calc
    _ = ∫ p : ℝ × Ioi (0 : ℝ), eightDAxialPositiveSubtypeIntegrand κ p
        ∂((volume : Measure ℝ).prod
          (Measure.comap (Subtype.val : Ioi (0 : ℝ) → ℝ) (volume : Measure ℝ))) := by
      exact integral_integral (f := fun s r => eightDAxialPositiveSubtypeIntegrand κ (s, r))
        (integrable_eightDAxialPositiveSubtypeIntegrand κ)
    _ = ∫ p : ℝ × Ioi (0 : ℝ), eightDAxialPlaneWeightedIntegrand κ (p.1, p.2)
        ∂((volume : Measure ℝ).prod
          (Measure.comap (Subtype.val : Ioi (0 : ℝ) → ℝ) (volume : Measure ℝ))) := by
      apply integral_congr_ae
      filter_upwards with p
      rfl
    _ = ∫ p in Set.univ ×ˢ Ioi (0 : ℝ),
        eightDAxialPlaneWeightedIntegrand κ p
        ∂((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
      rw [integral_positiveSubtype_prod_eq_setIntegral]
    _ = ∫ z, eightDAxialPositiveHalfPlaneIntegrand
        (eightDAxialPlaneWeightedIntegrand κ) z :=
      integral_upperHalfPlane_eq_complex _

/-- The real-valued surface measure of the unit five-sphere, computed from
Mathlib's `toSphere` construction and the eight-dimensional unit-ball volume. -/
theorem sphereEightMeasure_univ_real_copy :
    ((volume : Measure E₈).toSphere).real Set.univ = Real.pi ^ 4 / 3 := by
  rw [Measure.toSphere_real_apply_univ]
  have hdim : Module.finrank ℝ E₈ = 8 := by simp
  rw [hdim]
  change (8 : ℝ) * ENNReal.toReal (volume (Metric.ball (0 : E₈) 1)) = _
  rw [InnerProductSpace.volume_ball_of_dim_even (E := E₈) (k := 4) (by simp) 0 1]
  norm_num [ENNReal.toReal_mul]
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi ^ 4 / 24)]
  ring

/-- The area of the unit four-sphere, i.e. the angular `toSphere` mass in
five-dimensional Euclidean space. -/
theorem sphereSevenMeasure_univ_real_copy :
    ((volume : Measure E₇).toSphere).real Set.univ = (16 * Real.pi ^ 3) / 15 := by
  rw [Measure.toSphere_real_apply_univ]
  have hdim : Module.finrank ℝ E₇ = 7 := by simp
  rw [hdim]
  change (7 : ℝ) * ENNReal.toReal (volume (Metric.ball (0 : E₇) 1)) = _
  rw [InnerProductSpace.volume_ball_of_dim_odd (E := E₇) (k := 3) (by simp) 0 1]
  simp only [ENNReal.toReal_mul]
  norm_num [Nat.doubleFactorial]
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi ^ 3 * 16 / 105)]
  ring_nf

/-- Radial integration in E7 with the S6 factor made explicit. This is the
slice formula required after splitting E8 as one scalar plus seven residual
coordinates. -/
theorem integral_euclideanSeven_norm_radial (f : ℝ → ℝ) :
    (∫ y : E₇, f ‖y‖ ∂(volume : Measure E₇)) =
      (16 * Real.pi ^ 3 / 15) *
        ∫ r : Ioi (0 : ℝ), f r ∂(Measure.volumeIoiPow 6) := by
  rw [integral_euclidean_polarProduct (f := fun y : E₇ => f ‖y‖)]
  simp only [show Module.finrank ℝ E₇ - 1 = 6 by simp]
  calc
    (∫ p : Metric.sphere (0 : E₇) 1 × Ioi (0 : ℝ),
        f ‖(p.2 : ℝ) • (p.1 : E₇)‖ ∂
          ((volume : Measure E₇).toSphere.prod (Measure.volumeIoiPow 6))) =
        ∫ p : Metric.sphere (0 : E₇) 1 × Ioi (0 : ℝ), f p.2 ∂
          ((volume : Measure E₇).toSphere.prod (Measure.volumeIoiPow 6)) := by
      apply integral_congr_ae
      filter_upwards with p
      have hp : 0 < (p.2 : ℝ) := p.2.2
      have hu : ‖(p.1 : E₇)‖ = 1 := by
        simpa [dist_eq_norm] using p.1.2
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hp, hu, mul_one]
    _ = ((volume : Measure E₇).toSphere).real Set.univ •
          ∫ r : Ioi (0 : ℝ), f r ∂(Measure.volumeIoiPow 6) :=
        integral_fun_snd (μ := (volume : Measure E₇).toSphere)
          (ν := Measure.volumeIoiPow 6) (fun r : Ioi (0 : ℝ) => f r)
    _ = (16 * Real.pi ^ 3 / 15) *
          ∫ r : Ioi (0 : ℝ), f r ∂(Measure.volumeIoiPow 6) := by
      rw [smul_eq_mul, sphereSevenMeasure_univ_real_copy]

/-- Fubini plus E5 radial integration reduces the Cartesian test to the
scalar/radius half-plane integral. -/
theorem eightDAxialCartesianTest_integral_eq_scalar_radial (κ : ℝ) :
    (∫ x : E₈, eightDAxialCartesianTest κ x ∂(volume : Measure E₈)) =
      ∫ s : ℝ, (16 * Real.pi ^ 3 / 15) *
        ∫ r : Ioi (0 : ℝ), eightDAxialPlaneSlice κ s r
          ∂(Measure.volumeIoiPow 6) ∂(volume : Measure ℝ) := by
  rw [eightDAxialCartesianTest_integral_eq_planeSlice]
  calc
    _ = ∫ s : ℝ, ∫ y : E₇, eightDAxialPlaneSlice κ s ‖y‖
          ∂(volume : Measure E₇) ∂(volume : Measure ℝ) := by
      symm
      exact integral_integral
        (f := fun s y => eightDAxialPlaneSlice κ s ‖y‖)
        (integrable_eightDAxialPlaneIntegrand κ)
    _ = ∫ s : ℝ, (16 * Real.pi ^ 3 / 15) *
          ∫ r : Ioi (0 : ℝ), eightDAxialPlaneSlice κ s r
            ∂(Measure.volumeIoiPow 6) ∂(volume : Measure ℝ) := by
      apply integral_congr_ae
      filter_upwards with s
      exact integral_euclideanSeven_norm_radial (eightDAxialPlaneSlice κ s)

/-- Constant-function check for the S⁵ axial-angle density: its angular
weight has total mass exactly `π^3`, matching the actual `toSphere` measure. -/
theorem sphereEight_axial_weight_mass_copy :
    (16 * Real.pi ^ 3 / 15) * (∫ θ in (0 : ℝ)..Real.pi, Real.sin θ ^ 6) =
      Real.pi ^ 4 / 3 := by
  rw [integral_sin_pow]
  norm_num
  rw [integral_sin_pow]
  norm_num
  ring_nf

/-- Exact S⁵ axial-angle formula for the exponential test. The proof compares
the same compactly supported Cartesian integral through E6 polar coordinates
and through the E6 ≃ R×E5 split followed by the half-plane polar chart. -/
theorem sphereEightToSphereExpIntegral_eq_angleChart (κ : ℝ) :
    (∫ u : S₈, Real.exp (κ * (u : E₈) 0)
      ∂((volume : Measure E₈).toSphere)) =
      (16 * Real.pi ^ 3 / 15) *
        ∫ θ in (0 : ℝ)..Real.pi,
          Real.sin θ ^ 6 * Real.exp (κ * Real.cos θ) := by
  let cartesian : ℝ :=
    ∫ x : E₈, eightDAxialCartesianTest κ x ∂(volume : Measure E₈)
  let angular : ℝ :=
    ∫ u : S₈, Real.exp (κ * (u : E₈) 0)
      ∂((volume : Measure E₈).toSphere)
  have hchart : cartesian = (16 * Real.pi ^ 3 / 120) *
      ∫ θ in (0 : ℝ)..Real.pi, eightDAxialAngleFactor κ θ := by
    calc
      cartesian = ∫ s : ℝ, (16 * Real.pi ^ 3 / 15) *
          ∫ r : Ioi (0 : ℝ), eightDAxialPlaneSlice κ s r
            ∂(Measure.volumeIoiPow 6) ∂(volume : Measure ℝ) := by
        dsimp [cartesian]
        exact eightDAxialCartesianTest_integral_eq_scalar_radial κ
      _ = ∫ z, eightDAxialPositiveHalfPlaneIntegrand
          (eightDAxialPlaneWeightedIntegrand κ) z :=
        integral_eightDAxial_scalarRadial_eq_positiveHalfPlane κ
      _ = (16 * Real.pi ^ 3 / 120) *
          ∫ θ in (0 : ℝ)..Real.pi, eightDAxialAngleFactor κ θ :=
        integral_eightDAxialPlaneWeightedComplex_eq_angle κ
  dsimp only [eightDAxialAngleFactor] at hchart
  have hpolar : cartesian = angular * (1 / 8 : ℝ) := by
    dsimp [cartesian, angular]
    rw [eightDAxialCartesianTest_integral_factor κ]
    simp only [show Module.finrank ℝ E₈ - 1 = 7 by simp]
    rw [eightDAxialRadialCutoff_integral]
  dsimp [angular]
  nlinarith [hchart, hpolar]

end

end JinWishart.EightDAxial


