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

end

end JinWishart
