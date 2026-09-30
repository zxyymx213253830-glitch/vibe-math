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

/-- The polar-coordinate integrand of a shifted Gaussian cutoff is integrable
on the sphere-radius product. The cutoff confines the radius to a bounded
interval; `volumeIoiPow` gives that interval finite measure even though its
domain is the open ray. -/
theorem integrable_shiftedGaussianFourDBallPolarIntegrand
    (μ : EuclideanSpace ℝ (Fin 4)) (R : ℝ) (hR : 0 ≤ R) :
    Integrable
      (fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 × Ioi (0 : ℝ) =>
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) R).indicator
          (fun y => Real.exp (-‖y - μ‖ ^ 2 / 2))
          ((p.2 : ℝ) • (p.1 : EuclideanSpace ℝ (Fin 4))))
      ((volume : Measure (EuclideanSpace ℝ (Fin 4))).toSphere.prod
        (Measure.volumeIoiPow 3)) := by
  classical
  let f : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 × Ioi (0 : ℝ) → ℝ :=
    fun p => (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) R).indicator
      (fun y => Real.exp (-‖y - μ‖ ^ 2 / 2))
      ((p.2 : ℝ) • (p.1 : EuclideanSpace ℝ (Fin 4)))
  let ρ : Ioi (0 : ℝ) := ⟨R + 1,
    add_pos_of_nonneg_of_pos hR (by norm_num : (0 : ℝ) < 1)⟩
  let K : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 × Ioi (0 : ℝ)) :=
    Set.univ ×ˢ Set.Iio ρ
  have hmeas : Measurable f := by
    have hbody : Measurable (fun y : EuclideanSpace ℝ (Fin 4) =>
        Real.exp (-‖y - μ‖ ^ 2 / 2)) := by fun_prop
    have hcut : Measurable ((Metric.closedBall
        (0 : EuclideanSpace ℝ (Fin 4)) R).indicator
        (fun y => Real.exp (-‖y - μ‖ ^ 2 / 2))) :=
      hbody.indicator measurableSet_closedBall
    dsimp [f]
    exact hcut.comp (by fun_prop)
  have hbound : ∀ p, ‖f p‖ ≤ 1 := by
    intro p
    dsimp [f]
    rw [Set.indicator_apply]
    split_ifs with hp
    · rw [abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_one_iff.mpr
      nlinarith [sq_nonneg (‖(p.2 : ℝ) • (p.1 : EuclideanSpace ℝ (Fin 4)) - μ‖)]
    · simp
  have hsphere :
      ((volume : Measure (EuclideanSpace ℝ (Fin 4))).toSphere) Set.univ ≠ ⊤ := by
    exact ne_of_lt (measure_lt_top _ _)
  have hradius : (Measure.volumeIoiPow 3) (Set.Iio ρ) ≠ ⊤ := by
    rw [Measure.volumeIoiPow_apply_Iio]
    exact ENNReal.ofReal_ne_top
  have hKfinite :
      (((volume : Measure (EuclideanSpace ℝ (Fin 4))).toSphere).prod
        (Measure.volumeIoiPow 3)) K ≠ ⊤ := by
    change (((volume : Measure (EuclideanSpace ℝ (Fin 4))).toSphere).prod
      (Measure.volumeIoiPow 3)) (Set.univ ×ˢ Set.Iio ρ) ≠ ⊤
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top hsphere hradius
  have hboundAE : ∀ᵐ p ∂((((volume : Measure (EuclideanSpace ℝ (Fin 4))).toSphere).prod
      (Measure.volumeIoiPow 3)).restrict K), ‖f p‖ ≤ 1 :=
    Filter.Eventually.of_forall hbound
  have hlocal : IntegrableOn f K
      (((volume : Measure (EuclideanSpace ℝ (Fin 4))).toSphere).prod
        (Measure.volumeIoiPow 3)) :=
    Measure.integrableOn_of_bounded hKfinite hmeas.aestronglyMeasurable hboundAE
  have hzero : ∀ p, p ∉ K → f p = 0 := by
    intro p hp
    have hr : ¬ p.2 < ρ := by
      intro hh
      apply hp
      simp [K, hh]
    have hr' : R + 1 ≤ (p.2 : ℝ) := by
      have hsub : (ρ : ℝ) ≤ (p.2 : ℝ) := by
        exact_mod_cast (le_of_not_gt hr)
      simpa [ρ] using hsub
    have hu : ‖(p.1 : EuclideanSpace ℝ (Fin 4))‖ = 1 := by
      simpa [dist_eq_norm] using p.1.property
    have hrad : ‖(p.2 : ℝ) • (p.1 : EuclideanSpace ℝ (Fin 4))‖ = (p.2 : ℝ) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos p.2.property, hu, mul_one]
    have hout :
        ((p.2 : ℝ) • (p.1 : EuclideanSpace ℝ (Fin 4))) ∉
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) R := by
      intro hball
      have hdist : ‖(p.2 : ℝ) • (p.1 : EuclideanSpace ℝ (Fin 4))‖ ≤ R := by
        simpa [dist_eq_norm] using Metric.mem_closedBall.mp hball
      rw [hrad] at hdist
      linarith
    change (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) R).indicator
      (fun y => Real.exp (-‖y - μ‖ ^ 2 / 2))
      ((p.2 : ℝ) • (p.1 : EuclideanSpace ℝ (Fin 4))) = 0
    simp [Set.indicator, hout]
  exact hlocal.integrable_of_forall_notMem_eq_zero hzero

/-- Fubini may be applied to the polar decomposition of an actual shifted
Gaussian ball integral: the radius integral can be placed outside the sphere
integral. This is the analytic interface needed before evaluating each
spherical shell. -/
theorem shiftedGaussianFourDBallIntegral_eq_radiusSphereIntegral
    (μ : EuclideanSpace ℝ (Fin 4)) (R : ℝ) (hR : 0 ≤ R) :
    (∫ y, (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) R).indicator
        (fun y => Real.exp (-‖y - μ‖ ^ 2 / 2)) y ∂volume) =
      ∫ r : Ioi (0 : ℝ),
        ∫ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1,
          (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) R).indicator
            (fun y => Real.exp (-‖y - μ‖ ^ 2 / 2))
            ((r : ℝ) • (u : EuclideanSpace ℝ (Fin 4)))
          ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).toSphere)
        ∂(Measure.volumeIoiPow 3) := by
  let μS := (volume : Measure (EuclideanSpace ℝ (Fin 4))).toSphere
  let μR := Measure.volumeIoiPow 3
  let f : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 × Ioi (0 : ℝ) → ℝ :=
    fun p => (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) R).indicator
      (fun y => Real.exp (-‖y - μ‖ ^ 2 / 2))
      ((p.2 : ℝ) • (p.1 : EuclideanSpace ℝ (Fin 4)))
  have hpolar :
      (∫ y, (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) R).indicator
          (fun y => Real.exp (-‖y - μ‖ ^ 2 / 2)) y ∂volume) =
        ∫ p, f p ∂(μS.prod μR) := by
    simpa [f, μS, μR] using
      shiftedGaussianFourDBallIntegral_eq_sphereRadiusProduct μ R
  have hInt : Integrable (Function.uncurry (fun u r => f (u, r)))
      (μS.prod μR) := by
    have hpair : Integrable (fun p => f p) (μS.prod μR) := by
      simpa [f, μS, μR] using
        integrable_shiftedGaussianFourDBallPolarIntegrand μ R hR
    convert hpair using 1
    funext p
    rcases p with ⟨u, r⟩
    rfl
  calc
    _ = ∫ p, f p ∂(μS.prod μR) := hpolar
    _ = ∫ u, ∫ r, f (u, r) ∂μR ∂μS := (integral_integral hInt).symm
    _ = ∫ r, ∫ u, f (u, r) ∂μS ∂μR := integral_integral_swap hInt
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with r
      rfl

/-- On each positive-radius sphere, a centered ball cutoff is exactly the
radius condition `r ≤ R`. For an axial shift this identifies the cutoff
angular integral with the full Gaussian shell integral below the threshold. -/
theorem shiftedGaussianFourDBallSphereSlice_eq
    (a r R : ℝ) (hr : 0 < r) :
    (∫ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1,
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) R).indicator
        (fun y => Real.exp (-‖y -
          a • EuclideanSpace.single (0 : Fin 4) (1 : ℝ)‖ ^ 2 / 2))
        (r • (u : EuclideanSpace ℝ (Fin 4)))
      ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).toSphere)) =
      if r ≤ R then
        ∫ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1,
          Real.exp (-‖r • (u : EuclideanSpace ℝ (Fin 4)) -
            a • EuclideanSpace.single (0 : Fin 4) (1 : ℝ)‖ ^ 2 / 2)
          ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).toSphere)
      else 0 := by
  have hu (u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
      ‖(u : EuclideanSpace ℝ (Fin 4))‖ = 1 := by
    simpa [dist_eq_norm] using u.property
  have hrad (u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
      dist (r • (u : EuclideanSpace ℝ (Fin 4))) 0 = r := by
    rw [dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
      hu u, mul_one]
  have hmem (u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
      r • (u : EuclideanSpace ℝ (Fin 4)) ∈
        Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) R ↔ r ≤ R := by
    rw [Metric.mem_closedBall, hrad u]
  by_cases hcut : r ≤ R
  · have hpoint (u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) R).indicator
          (fun y => Real.exp (-‖y -
            a • EuclideanSpace.single (0 : Fin 4) (1 : ℝ)‖ ^ 2 / 2))
          (r • (u : EuclideanSpace ℝ (Fin 4))) =
        Real.exp (-‖r • (u : EuclideanSpace ℝ (Fin 4)) -
          a • EuclideanSpace.single (0 : Fin 4) (1 : ℝ)‖ ^ 2 / 2) := by
      simp [Set.indicator, hmem u, hcut]
    calc
      _ = ∫ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1,
          Real.exp (-‖r • (u : EuclideanSpace ℝ (Fin 4)) -
            a • EuclideanSpace.single (0 : Fin 4) (1 : ℝ)‖ ^ 2 / 2)
          ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).toSphere) := by
        apply integral_congr_ae
        filter_upwards with u
        exact hpoint u
      _ = _ := by simp [hcut]
  · have hpoint (u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) R).indicator
          (fun y => Real.exp (-‖y -
            a • EuclideanSpace.single (0 : Fin 4) (1 : ℝ)‖ ^ 2 / 2))
          (r • (u : EuclideanSpace ℝ (Fin 4))) = 0 := by
      simp [Set.indicator, hmem u, hcut]
    calc
      _ = ∫ u : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1, (0 : ℝ)
          ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).toSphere) := by
        apply integral_congr_ae
        filter_upwards with u
        exact hpoint u
      _ = 0 := by simp
      _ = _ := by simp [hcut]

end JinWishart
