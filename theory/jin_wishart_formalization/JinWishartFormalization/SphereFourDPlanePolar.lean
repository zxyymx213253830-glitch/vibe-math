import JinWishartFormalization.SphereFourDAngularIntegral
import Mathlib.Analysis.SpecialFunctions.PolarCoord

open MeasureTheory Set

namespace JinWishart

noncomputable section

local notation "E₄" => EuclideanSpace ℝ (Fin 4)
local notation "S₄" => Metric.sphere (0 : E₄) 1
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

theorem euclideanFourToRealProdThree_symm_apply_zero (s : ℝ) (y : E₃) :
    (euclideanFourToRealProdThree.symm (s, y) : E₄) 0 = s := by
  simp [euclideanFourToRealProdThree, MeasurableEquiv.prodCongr]

theorem euclideanFourToRealProdThree_norm_sq (s : ℝ) (y : E₃) :
    ‖(euclideanFourToRealProdThree.symm (s, y) : E₄)‖ ^ 2 =
      s ^ 2 + ‖y‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp [euclideanFourToRealProdThree, MeasurableEquiv.prodCongr,
    Fin.sum_univ_succ]

theorem euclideanFourToRealProdThree_norm (s : ℝ) (y : E₃) :
    ‖(euclideanFourToRealProdThree.symm (s, y) : E₄)‖ =
      Real.sqrt (s ^ 2 + ‖y‖ ^ 2) := by
  have hsq := euclideanFourToRealProdThree_norm_sq s y
  have hnorm : 0 ≤ ‖(euclideanFourToRealProdThree.symm (s, y) : E₄)‖ := norm_nonneg _
  have hsqrt : 0 ≤ Real.sqrt (s ^ 2 + ‖y‖ ^ 2) := Real.sqrt_nonneg _
  nlinarith [Real.sq_sqrt (show 0 ≤ s ^ 2 + ‖y‖ ^ 2 by positivity)]

theorem euclideanFourToRealProdThree_origin_iff (s : ℝ) (y : E₃) :
    euclideanFourToRealProdThree.symm (s, y) = 0 ↔ s = 0 ∧ ‖y‖ = 0 := by
  have hnorm := euclideanFourToRealProdThree_norm s y
  constructor
  · intro hx
    have hzero : Real.sqrt (s ^ 2 + ‖y‖ ^ 2) = 0 := by
      rw [← hnorm]
      simp [hx]
    have hle : s ^ 2 + ‖y‖ ^ 2 ≤ 0 := (Real.sqrt_eq_zero').mp hzero
    have hnonneg : 0 ≤ s ^ 2 + ‖y‖ ^ 2 := by positivity
    have hsum : s ^ 2 + ‖y‖ ^ 2 = 0 := le_antisymm hle hnonneg
    constructor <;> nlinarith [sq_nonneg s, sq_nonneg ‖y‖, hsum]
  · rintro ⟨rfl, hy⟩
    apply norm_eq_zero.mp
    rw [hnorm]
    simp [hy]

/-- The angular cutoff test expressed in the separated scalar/radial
coordinates. The zero vector branch matches the original test definition. -/
def fourDAngularPlaneSlice (κ s ρ : ℝ) : ℝ :=
  if s = 0 ∧ ρ = 0 then 0
  else if Real.sqrt (s ^ 2 + ρ ^ 2) < 1 then
    Real.exp (κ * (s / Real.sqrt (s ^ 2 + ρ ^ 2)))
  else 0

theorem fourDAngularCartesianTest_eq_planeSlice (κ s : ℝ) (y : E₃) :
    fourDAngularCartesianTest κ
        (euclideanFourToRealProdThree.symm (s, y)) =
      fourDAngularPlaneSlice κ s ‖y‖ := by
  have hcoord := euclideanFourToRealProdThree_symm_apply_zero s y
  have hnorm := euclideanFourToRealProdThree_norm s y
  have horigin := euclideanFourToRealProdThree_origin_iff s y
  by_cases hs : s = 0 ∧ ‖y‖ = 0
  · have hx0 : euclideanFourToRealProdThree.symm (s, y) = 0 := horigin.mpr hs
    rw [fourDAngularCartesianTest, dif_pos hx0, fourDAngularPlaneSlice]
    simp [hs]
  · have hx : euclideanFourToRealProdThree.symm (s, y) ≠ 0 := by
      intro h
      exact hs (horigin.mp h)
    rw [fourDAngularCartesianTest, dif_neg hx, fourDAngularPlaneSlice, if_neg hs]
    rw [hnorm, hcoord]

/-- The four-dimensional Cartesian test integral after the measure-preserving
coordinate split `E₄ ≃ ℝ × E₃`. This exposes the scalar/radial slice integral
needed for the subsequent Fubini and planar-polar calculation. -/
theorem fourDAngularCartesianTest_integral_eq_planeSlice (κ : ℝ) :
    (∫ x : E₄, fourDAngularCartesianTest κ x ∂(volume : Measure E₄)) =
      ∫ p : ℝ × E₃, fourDAngularPlaneSlice κ p.1 ‖p.2‖
        ∂((volume : Measure ℝ).prod (volume : Measure E₃)) := by
  rw [integral_euclideanFour_eq_integral_realProdThree]
  apply integral_congr_ae
  filter_upwards with p
  exact fourDAngularCartesianTest_eq_planeSlice κ p.1 p.2

/-- For each fixed scalar coordinate, the remaining three-dimensional slice
integral is exactly radial, with the S² mass `4π` as its angular factor. -/
theorem fourDAngularPlaneSlice_integral_three (κ s : ℝ) :
    (∫ y : E₃, fourDAngularPlaneSlice κ s ‖y‖ ∂(volume : Measure E₃)) =
      4 * Real.pi * ∫ r : Ioi (0 : ℝ), fourDAngularPlaneSlice κ s r
        ∂(Measure.volumeIoiPow 2) := by
  exact integral_euclideanThree_norm_radial (fourDAngularPlaneSlice κ s)

def fourDAngularPlaneIntegrand (κ : ℝ) (p : ℝ × E₃) : ℝ :=
  fourDAngularPlaneSlice κ p.1 ‖p.2‖

theorem measurable_fourDAngularPlaneIntegrand (κ : ℝ) :
    Measurable (fourDAngularPlaneIntegrand κ) := by
  unfold fourDAngularPlaneIntegrand fourDAngularPlaneSlice
  refine Measurable.ite (by measurability) measurable_const ?_
  refine Measurable.ite (by measurability) ?_ measurable_const
  fun_prop

theorem fourDAngularPlaneIntegrand_norm_le (κ : ℝ) (p : ℝ × E₃) :
    ‖fourDAngularPlaneIntegrand κ p‖ ≤ Real.exp |κ| := by
  dsimp [fourDAngularPlaneIntegrand, fourDAngularPlaneSlice]
  by_cases hzero : p.1 = 0 ∧ ‖p.2‖ = 0
  · simp [hzero]
    positivity
  · by_cases hball : Real.sqrt (p.1 ^ 2 + ‖p.2‖ ^ 2) < 1
    · have hsum : 0 < p.1 ^ 2 + ‖p.2‖ ^ 2 := by
        by_contra h
        have hle : p.1 ^ 2 + ‖p.2‖ ^ 2 ≤ 0 := le_of_not_gt h
        have heq : p.1 ^ 2 + ‖p.2‖ ^ 2 = 0 := le_antisymm hle (by positivity)
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
          _ ≤ |κ| := by
            calc
              _ ≤ |κ| * 1 := mul_le_mul_of_nonneg_left hratio (abs_nonneg κ)
              _ = |κ| := mul_one _
      rw [if_neg hzero, if_pos hball]
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr hprod
    · simp [hzero, hball]
      positivity

theorem integrable_fourDAngularPlaneIntegrand (κ : ℝ) :
    Integrable (fourDAngularPlaneIntegrand κ)
      ((volume : Measure ℝ).prod (volume : Measure E₃)) := by
  let rect : Set (ℝ × E₃) := Icc (-1 : ℝ) 1 ×ˢ Metric.closedBall (0 : E₃) 1
  have hcompact : IsCompact rect := by
    dsimp [rect]
    exact isCompact_Icc.prod (isCompact_closedBall 0 1)
  have hfinite : ((volume : Measure ℝ).prod (volume : Measure E₃)) rect ≠ ⊤ :=
    hcompact.measure_ne_top
  have hmeas := measurable_fourDAngularPlaneIntegrand κ
  have hbound : ∀ᵐ p ∂(((volume : Measure ℝ).prod (volume : Measure E₃)).restrict rect),
      ‖fourDAngularPlaneIntegrand κ p‖ ≤ Real.exp |κ| :=
    Filter.Eventually.of_forall fun p => fourDAngularPlaneIntegrand_norm_le κ p
  have hion : IntegrableOn (fourDAngularPlaneIntegrand κ) rect
      ((volume : Measure ℝ).prod (volume : Measure E₃)) :=
    Measure.integrableOn_of_bounded hfinite hmeas.aestronglyMeasurable hbound
  have hzero_outside : ∀ p, p ∉ rect → fourDAngularPlaneIntegrand κ p = 0 := by
    rintro ⟨s, y⟩ hp
    by_contra hne
    have hball : Real.sqrt (s ^ 2 + ‖y‖ ^ 2) < 1 := by
      by_contra hb
      by_cases hz : s = 0 ∧ ‖y‖ = 0
      · simp [fourDAngularPlaneIntegrand, fourDAngularPlaneSlice, hz] at hne
      · simp [fourDAngularPlaneIntegrand, fourDAngularPlaneSlice, hz, hb] at hne
    have hsabs : |s| ≤ Real.sqrt (s ^ 2 + ‖y‖ ^ 2) :=
      Real.abs_le_sqrt (by nlinarith [sq_nonneg ‖y‖])
    have hybound : ‖y‖ ≤ Real.sqrt (s ^ 2 + ‖y‖ ^ 2) :=
      Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg s])
    have hslo : -1 ≤ s := by nlinarith [abs_le.mp hsabs]
    have hshi : s ≤ 1 := by nlinarith [abs_le.mp hsabs]
    have hymem : y ∈ Metric.closedBall (0 : E₃) 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      nlinarith
    have hmem : (s, y) ∈ rect := ⟨⟨hslo, hshi⟩, hymem⟩
    exact hp hmem
  exact hion.integrable_of_forall_notMem_eq_zero hzero_outside

/-- Fubini followed by the three-dimensional radial formula reduces the
Cartesian angular test to a scalar coordinate and a nonnegative radius. -/
theorem fourDAngularCartesianTest_integral_eq_scalar_radial (κ : ℝ) :
    (∫ x : E₄, fourDAngularCartesianTest κ x ∂(volume : Measure E₄)) =
      ∫ s : ℝ, 4 * Real.pi *
        ∫ r : Ioi (0 : ℝ), fourDAngularPlaneSlice κ s r
          ∂(Measure.volumeIoiPow 2) ∂(volume : Measure ℝ) := by
  rw [fourDAngularCartesianTest_integral_eq_planeSlice]
  calc
    _ = ∫ s : ℝ, ∫ y : E₃, fourDAngularPlaneSlice κ s ‖y‖
          ∂(volume : Measure E₃) ∂(volume : Measure ℝ) := by
      symm
      exact integral_integral
        (f := fun s y => fourDAngularPlaneSlice κ s ‖y‖)
        (integrable_fourDAngularPlaneIntegrand κ)
    _ = ∫ s : ℝ, 4 * Real.pi *
          ∫ r : Ioi (0 : ℝ), fourDAngularPlaneSlice κ s r
            ∂(Measure.volumeIoiPow 2) ∂(volume : Measure ℝ) := by
      apply integral_congr_ae
      filter_upwards with s
      exact fourDAngularPlaneSlice_integral_three κ s

end

end JinWishart
