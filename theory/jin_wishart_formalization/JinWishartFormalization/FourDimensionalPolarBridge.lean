import JinWishartFormalization.NoncentralFourDimensionalSphere
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# Exact four-dimensional polar decomposition into sphere × radius

This module uses Mathlib's `Measure.toSphere` and
`measurePreserving_homeomorphUnitSphereProd` to obtain a genuine geometric
change-of-variables statement. The S³ angular factor is identified with its
single-angle chart in `SphereFourDPlaneAngleChart.lean`; the proof uses
Fubini and measure-transport steps that remain on the repository's
`[需人工审查]` checklist.
-/

open MeasureTheory Set

namespace JinWishart

private theorem norm_smul_inv_norm_smul_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : E} (hx : x ≠ 0) : ‖x‖ • (‖x‖⁻¹ • x) = x := by
  rw [smul_smul]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  simp [hn]

theorem integral_euclidean_polarProduct
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) :
    (∫ x, f x ∂(volume : Measure E)) =
      ∫ p : Metric.sphere (0 : E) 1 × Ioi (0 : ℝ),
        f ((p.2 : ℝ) • (p.1 : E)) ∂
          ((volume : Measure E).toSphere.prod
            (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
  calc
    (∫ x, f x ∂(volume : Measure E)) =
        ∫ x : ({0}ᶜ : Set E), f x.1 ∂((volume : Measure E).comap Subtype.val) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl (fun x => f x),
        restrict_compl_singleton]
    _ = ∫ x : ({0}ᶜ : Set E),
        f (‖(x : E)‖ • (‖(x : E)‖⁻¹ • (x : E)))
          ∂((volume : Measure E).comap Subtype.val) := by
      apply integral_congr_ae
      filter_upwards with x
      exact congrArg f (norm_smul_inv_norm_smul_eq x.2).symm
    _ = ∫ p : Metric.sphere (0 : E) 1 × Ioi (0 : ℝ),
        f ((p.2 : ℝ) • (p.1 : E)) ∂
          ((volume : Measure E).toSphere.prod
            (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
      simpa only [homeomorphUnitSphereProd_apply_fst_coe,
        homeomorphUnitSphereProd_apply_snd_coe] using
        (Measure.measurePreserving_homeomorphUnitSphereProd
          (μ := (volume : Measure E))).integral_comp
          (Homeomorph.measurableEmbedding _)
          (fun p : Metric.sphere (0 : E) 1 × Ioi (0 : ℝ) =>
            f ((p.2 : ℝ) • (p.1 : E)))

/-- A shifted Gaussian ball integral in four real coordinates, written exactly
as the product of Mathlib's unit-sphere measure and radial measure. This is a
change-of-variables theorem; only the subsequent evaluation of its sphere
integral is left open. -/
theorem shiftedGaussianFourDBallIntegral_eq_sphereRadiusProduct
    (μ : EuclideanSpace ℝ (Fin 4)) (R : ℝ) :
    (∫ y, (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) R).indicator
        (fun y => Real.exp (-‖y - μ‖ ^ 2 / 2)) y ∂volume) =
      ∫ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 × Ioi (0 : ℝ),
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) R).indicator
          (fun y => Real.exp (-‖y - μ‖ ^ 2 / 2))
          ((p.2 : ℝ) • (p.1 : EuclideanSpace ℝ (Fin 4))) ∂
          ((volume : Measure (EuclideanSpace ℝ (Fin 4))).toSphere.prod
            (Measure.volumeIoiPow 3)) := by
  simpa using integral_euclidean_polarProduct
    (f := fun y : EuclideanSpace ℝ (Fin 4) =>
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) R).indicator
        (fun y => Real.exp (-‖y - μ‖ ^ 2 / 2)) y)

end JinWishart
