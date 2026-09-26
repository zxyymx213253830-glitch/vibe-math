import JinWishartFormalization.FourDimensionalPolarBridge
import JinWishartFormalization.SphereThreeMeasure
import JinWishartFormalization.BesselI1Angle

open MeasureTheory Set

namespace JinWishart

noncomputable section

local notation "E₄" => EuclideanSpace ℝ (Fin 4)
local notation "S₄" => Metric.sphere (0 : E₄) 1
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

/-- Coordinates separating the first real coordinate from the remaining three. -/
noncomputable def euclideanFourToRealProdThree : E₄ ≃ᵐ ℝ × E₃ :=
  (MeasurableEquiv.toLp 2 (Fin 4 → ℝ)).symm.trans <|
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).trans <|
      MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))

/-- The coordinate equivalence is measure preserving for Euclidean volumes. -/
theorem euclideanFourToRealProdThree_measurePreserving :
    MeasurePreserving euclideanFourToRealProdThree
      (volume : Measure E₄) ((volume : Measure ℝ).prod (volume : Measure E₃)) := by
  dsimp [euclideanFourToRealProdThree]
  exact (PiLp.volume_preserving_ofLp (ι := Fin 4)).trans <|
    (volume_preserving_piFinSuccAbove (fun _ : Fin 4 => ℝ) 0).trans <|
      MeasurePreserving.prod (MeasurePreserving.id volume)
        (PiLp.volume_preserving_toLp (Fin 3))

/-- Integral form of `euclideanFourToRealProdThree_measurePreserving`. -/
theorem integral_euclideanFour_eq_integral_realProdThree (f : E₄ → ℝ) :
    (∫ x, f x ∂(volume : Measure E₄)) =
      ∫ p : ℝ × E₃, f (euclideanFourToRealProdThree.symm p)
        ∂((volume : Measure ℝ).prod (volume : Measure E₃)) := by
  symm
  exact euclideanFourToRealProdThree_measurePreserving.symm.integral_comp
    (MeasurableEquiv.measurableEmbedding euclideanFourToRealProdThree.symm) f

/-- A generic factorization consequence of the existing four-dimensional
polar decomposition. The pointwise hypothesis is the only connection between
the Cartesian integrand and its angular/radial factors. -/
theorem integral_euclidean_fourD_polar_factor
    (f : E₄ → ℝ) (g : S₄ → ℝ) (h : Ioi (0 : ℝ) → ℝ)
    (hfactor : ∀ p : S₄ × Ioi (0 : ℝ),
      f ((p.2 : ℝ) • (p.1 : E₄)) = g p.1 * h p.2) :
    (∫ x, f x ∂(volume : Measure E₄)) =
      (∫ u, g u ∂((volume : Measure E₄).toSphere)) *
        ∫ r, h r ∂(Measure.volumeIoiPow (Module.finrank ℝ E₄ - 1)) := by
  rw [integral_euclidean_polarProduct (f := f)]
  calc
    (∫ p : S₄ × Ioi (0 : ℝ),
        f ((p.2 : ℝ) • (p.1 : E₄)) ∂
          ((volume : Measure E₄).toSphere.prod
            (Measure.volumeIoiPow (Module.finrank ℝ E₄ - 1)))) =
        ∫ p : S₄ × Ioi (0 : ℝ), g p.1 * h p.2 ∂
          ((volume : Measure E₄).toSphere.prod
            (Measure.volumeIoiPow (Module.finrank ℝ E₄ - 1))) := by
      apply integral_congr_ae
      filter_upwards with p
      exact hfactor p
    _ = (∫ u, g u ∂((volume : Measure E₄).toSphere)) *
          ∫ r, h r ∂(Measure.volumeIoiPow (Module.finrank ℝ E₄ - 1)) :=
        integral_prod_mul g h

/-- The radial cutoff used to obtain a nonzero, finite radial factor. -/
def fourDAngularRadialCutoff (r : Ioi (0 : ℝ)) : ℝ :=
  (Iio (⟨1, mem_Ioi.mpr one_pos⟩ : Ioi (0 : ℝ))).indicator (fun _ => 1) r

/-- The radial factor for the unit-ball cutoff is exactly `1/4`. -/
theorem fourDAngularRadialCutoff_integral :
    (∫ r : Ioi (0 : ℝ), fourDAngularRadialCutoff r
      ∂(Measure.volumeIoiPow 3)) = (1 / 4 : ℝ) := by
  calc
    (∫ r : Ioi (0 : ℝ), fourDAngularRadialCutoff r
        ∂(Measure.volumeIoiPow 3)) =
      ∫ r : Ioi (0 : ℝ),
        (Iio (⟨1, mem_Ioi.mpr one_pos⟩ : Ioi (0 : ℝ))).indicator
          (1 : Ioi (0 : ℝ) → ℝ) r ∂(Measure.volumeIoiPow 3) := rfl
    _ = (Measure.volumeIoiPow 3).real (Iio (⟨1, mem_Ioi.mpr one_pos⟩ : Ioi (0 : ℝ))) :=
      integral_indicator_one measurableSet_Iio
    _ = (1 / 4 : ℝ) := by
      norm_num [Measure.real, Measure.volumeIoiPow_apply_Iio]

/-- A Cartesian test function whose four-dimensional polar form is the product
of the requested spherical exponential and a unit-radius radial cutoff. -/
def fourDAngularCartesianTest (κ : ℝ) (x : E₄) : ℝ :=
  if hx : x = 0 then 0
  else if ‖x‖ < 1 then Real.exp (κ * (x 0 / ‖x‖)) else 0

theorem fourDAngularCartesianTest_smul_factor
    (κ : ℝ) (u : S₄) (r : Ioi (0 : ℝ)) :
    fourDAngularCartesianTest κ ((r : ℝ) • (u : E₄)) =
      Real.exp (κ * (u : E₄) 0) * fourDAngularRadialCutoff r := by
  have hr : 0 < (r : ℝ) := r.2
  have hu : ‖(u : E₄)‖ = 1 := by
    simpa [dist_eq_norm] using u.2
  have hnorm : ‖(r : ℝ) • (u : E₄)‖ = (r : ℝ) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hu, mul_one]
  have hne : (r : ℝ) • (u : E₄) ≠ 0 := by
    intro hz
    have hz' : ‖(r : ℝ) • (u : E₄)‖ = 0 := by simpa using congrArg norm hz
    rw [hnorm] at hz'
    linarith
  have hune : (u : E₄) ≠ 0 := by
    intro hz
    have hz' : ‖(u : E₄)‖ = 0 := by simpa using congrArg norm hz
    rw [hu] at hz'
    norm_num at hz'
  have hcoord : ((r : ℝ) • (u : E₄)) 0 / ‖(r : ℝ) • (u : E₄)‖ = (u : E₄) 0 := by
    rw [hnorm]
    change ((r : ℝ) * (u : E₄).ofLp 0) / (r : ℝ) = (u : E₄).ofLp 0
    field_simp [ne_of_gt hr]
  by_cases hr1 : (r : ℝ) < 1
  · have hlt : ‖(r : ℝ) • (u : E₄)‖ < 1 := by simpa [hnorm] using hr1
    have hcut : r ∈ Iio (⟨1, mem_Ioi.mpr one_pos⟩ : Ioi (0 : ℝ)) := by
      change (r : ℝ) < 1
      exact hr1
    simp only [fourDAngularCartesianTest, dif_neg hne, if_pos hlt]
    rw [hcoord]
    change Real.exp (κ * (u : E₄) 0) =
      Real.exp (κ * (u : E₄) 0) *
        (Iio (⟨1, mem_Ioi.mpr one_pos⟩ : Ioi (0 : ℝ))).indicator (fun _ => 1) r
    rw [Set.indicator_of_mem hcut]
    simp
  · have hnotlt : ¬‖(r : ℝ) • (u : E₄)‖ < 1 := by simpa [hnorm] using hr1
    have hcut : r ∉ Iio (⟨1, mem_Ioi.mpr one_pos⟩ : Ioi (0 : ℝ)) := by
      change ¬(r : ℝ) < 1
      exact hr1
    simp only [fourDAngularCartesianTest, dif_neg hne, if_neg hnotlt]
    change (0 : ℝ) =
      Real.exp (κ * (u : E₄) 0) *
        (Iio (⟨1, mem_Ioi.mpr one_pos⟩ : Ioi (0 : ℝ))).indicator (fun _ => 1) r
    rw [Set.indicator_of_notMem hcut]
    simp

/-- Exact Cartesian-to-spherical reduction for the factorized test function.
This is an intermediate step toward identifying the `toSphere` integral with
the single-angle chart integral. -/
theorem fourDAngularCartesianTest_integral_factor (κ : ℝ) :
    (∫ x, fourDAngularCartesianTest κ x ∂(volume : Measure E₄)) =
      (∫ u : S₄, Real.exp (κ * (u : E₄) 0)
        ∂((volume : Measure E₄).toSphere)) *
        ∫ r : Ioi (0 : ℝ), fourDAngularRadialCutoff r
          ∂(Measure.volumeIoiPow (Module.finrank ℝ E₄ - 1)) := by
  apply integral_euclidean_fourD_polar_factor
  intro p
  exact fourDAngularCartesianTest_smul_factor κ p.1 p.2

end

end JinWishart
