import JinWishartFormalization.SphereEightDAxialPushforward
import JinWishartFormalization.NoncentralEvenDimensionalPoissonMixture
import JinWishartFormalization.EightDimensionalAngularBesselI3

/-!
# Eight-dimensional shifted Gaussian shell kernel

This module connects the actual `toSphere` measure on `S⁷` to the general
even-dimensional noncentral radial kernel. It closes the angular shell
identity, but not yet the integration over radii required for a ball CDF.
-/

open MeasureTheory Set

namespace JinWishart

noncomputable section

local notation "E₈" => EuclideanSpace ℝ (Fin 8)
local notation "S₈" => Metric.sphere (0 : E₈) 1

/-- Squared distance from a polar point to a first-axis center in eight real
dimensions. -/
theorem eightDDistance_sq_sub_firstAxis (u : S₈) (r a : ℝ) :
    ‖r • (u : E₈) - a • EuclideanSpace.single (0 : Fin 8) (1 : ℝ)‖ ^ 2 =
      r ^ 2 + a ^ 2 - 2 * a * r * (u : E₈) 0 := by
  have hu : ‖(u : E₈)‖ = 1 := by
    simpa [dist_eq_norm] using u.property
  rw [norm_sub_sq_real, norm_smul, norm_smul, hu]
  rw [real_inner_smul_left, real_inner_smul_right]
  simp [Real.norm_eq_abs, EuclideanSpace.inner_single_right]
  ring_nf

/-- The S⁷ angular integral of an axially shifted Gaussian shell, expressed
through the rigorously established `sin⁶` chart. -/
theorem eightDShiftedGaussianAngularIntegral_eq_chart (a r : ℝ) :
    (∫ u : S₈,
      Real.exp (-‖r • (u : E₈) -
        a • EuclideanSpace.single (0 : Fin 8) (1 : ℝ)‖ ^ 2 / 2)
      ∂((volume : Measure E₈).toSphere)) =
      Real.exp (-((r ^ 2 + a ^ 2) / 2)) *
        ((16 * Real.pi ^ 3 / 15) *
          ∫ θ in (0 : ℝ)..Real.pi,
            Real.sin θ ^ 6 * Real.exp (a * r * Real.cos θ)) := by
  calc
    _ = ∫ u : S₈,
        Real.exp (-((r ^ 2 + a ^ 2) / 2)) *
          Real.exp (a * r * (u : E₈) 0)
        ∂((volume : Measure E₈).toSphere) := by
      apply integral_congr_ae
      filter_upwards with u
      rw [eightDDistance_sq_sub_firstAxis]
      have he : -(r ^ 2 + a ^ 2 - 2 * a * r * (u : E₈) 0) / 2 =
          -((r ^ 2 + a ^ 2) / 2) + a * r * (u : E₈) 0 := by ring
      rw [he, Real.exp_add]
    _ = Real.exp (-((r ^ 2 + a ^ 2) / 2)) *
        (∫ u : S₈, Real.exp (a * r * (u : E₈) 0)
          ∂((volume : Measure E₈).toSphere)) := by
      rw [integral_const_mul]
    _ = _ := by
      rw [JinWishart.EightDAxial.sphereEightToSphereExpIntegral_eq_angleChart,
        angularSinSixIntegral_eq_besselI3FactorialSeries]

/-- The eight-dimensional standard-Gaussian shell, including its radial
Jacobian and normalizer, equals the general even-dimensional factorial
kernel at `k=3`. -/
theorem eightDShiftedGaussianShell_eq_radialKernel (a r : ℝ) :
    (2 * Real.pi)⁻¹ ^ 4 * r ^ 7 *
      (∫ u : S₈,
        Real.exp (-‖r • (u : E₈) -
          a • EuclideanSpace.single (0 : Fin 8) (1 : ℝ)‖ ^ 2 / 2)
        ∂((volume : Measure E₈).toSphere)) =
      noncentralChiEvenRadialKernel 3 a r := by
  rw [eightDShiftedGaussianAngularIntegral_eq_chart,
    angularSinSixIntegral_eq_besselI3FactorialSeries]
  unfold noncentralChiEvenRadialKernel
  field_simp [Real.pi_ne_zero]
  ring

/-- Unfolding the eight-dimensional radial measure gives the usual r⁷
Jacobian on positive radii. -/
theorem integral_volumeIoiPow_seven_eq_Ioi (f : Ioi (0 : ℝ) → ℝ) :
    (∫ r, f r ∂(Measure.volumeIoiPow 7)) =
      ∫ r : Ioi (0 : ℝ), (r : ℝ) ^ 7 * f r
        ∂(Measure.comap Subtype.val (volume : Measure ℝ)) := by
  rw [Measure.volumeIoiPow, integral_withDensity_eq_integral_toReal_smul]
  · congr 1
    funext r
    have hr : 0 < (r : ℝ) := r.property
    simp only [ENNReal.toReal_ofReal (pow_nonneg hr.le 7)]
    simp [smul_eq_mul]
  · fun_prop
  · filter_upwards with r
    simp

/-- The centered-ball cutoff is integrable on the S⁷/radius product: the
radius is confined to a bounded interval and the Gaussian factor is at most
one. -/
theorem integrable_eightDShiftedGaussianBallPolarIntegrand
    (a R : ℝ) (hR : 0 ≤ R) :
    Integrable
      (fun p : S₈ × Ioi (0 : ℝ) =>
        (Metric.closedBall (0 : E₈) R).indicator
          (fun y : E₈ => Real.exp (-‖y -
            a • EuclideanSpace.single (0 : Fin 8) (1 : ℝ)‖ ^ 2 / 2))
          ((p.2 : ℝ) • (p.1 : E₈)))
      (((volume : Measure E₈).toSphere).prod (Measure.volumeIoiPow 7)) := by
  classical
  let f : S₈ × Ioi (0 : ℝ) → ℝ := fun p =>
    (Metric.closedBall (0 : E₈) R).indicator
      (fun y : E₈ => Real.exp (-‖y -
        a • EuclideanSpace.single (0 : Fin 8) (1 : ℝ)‖ ^ 2 / 2))
      ((p.2 : ℝ) • (p.1 : E₈))
  let ρ : Ioi (0 : ℝ) := ⟨R + 1,
    add_pos_of_nonneg_of_pos hR (by norm_num : (0 : ℝ) < 1)⟩
  let K : Set (S₈ × Ioi (0 : ℝ)) := Set.univ ×ˢ Set.Iio ρ
  have hmeas : Measurable f := by
    have hbody : Measurable (fun y : E₈ => Real.exp (-‖y -
        a • EuclideanSpace.single (0 : Fin 8) (1 : ℝ)‖ ^ 2 / 2)) := by fun_prop
    have hcut : Measurable ((Metric.closedBall (0 : E₈) R).indicator
        (fun y : E₈ => Real.exp (-‖y -
          a • EuclideanSpace.single (0 : Fin 8) (1 : ℝ)‖ ^ 2 / 2))) :=
      hbody.indicator measurableSet_closedBall
    dsimp [f]
    exact hcut.comp (by fun_prop)
  have hbound (p : S₈ × Ioi (0 : ℝ)) : ‖f p‖ ≤ 1 := by
    dsimp [f]
    rw [Set.indicator_apply]
    split_ifs with hp
    · rw [abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_one_iff.mpr
      nlinarith [sq_nonneg (‖((p.2 : ℝ) • (p.1 : E₈)) -
        a • EuclideanSpace.single (0 : Fin 8) (1 : ℝ)‖)]
    · simp
  have hsphere : ((volume : Measure E₈).toSphere) Set.univ ≠ ⊤ :=
    ne_of_lt (measure_lt_top _ _)
  have hradius : (Measure.volumeIoiPow 7) (Set.Iio ρ) ≠ ⊤ := by
    rw [Measure.volumeIoiPow_apply_Iio]
    exact ENNReal.ofReal_ne_top
  have hKfinite :
      ((((volume : Measure E₈).toSphere).prod (Measure.volumeIoiPow 7)) K) ≠ ⊤ := by
    change ((((volume : Measure E₈).toSphere).prod (Measure.volumeIoiPow 7))
      (Set.univ ×ˢ Set.Iio ρ)) ≠ ⊤
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top hsphere hradius
  have hboundAE : ∀ᵐ p ∂((((volume : Measure E₈).toSphere).prod
      (Measure.volumeIoiPow 7)).restrict K), ‖f p‖ ≤ 1 :=
    Filter.Eventually.of_forall hbound
  have hlocal : IntegrableOn f K
      (((volume : Measure E₈).toSphere).prod (Measure.volumeIoiPow 7)) :=
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
    have hu : ‖(p.1 : E₈)‖ = 1 := by
      simpa [dist_eq_norm] using p.1.property
    have hrad : ‖(p.2 : ℝ) • (p.1 : E₈)‖ = (p.2 : ℝ) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos p.2.property, hu, mul_one]
    have hout : ((p.2 : ℝ) • (p.1 : E₈)) ∉ Metric.closedBall (0 : E₈) R := by
      intro hball
      have hdist : ‖(p.2 : ℝ) • (p.1 : E₈)‖ ≤ R := by
        simpa [dist_eq_norm] using Metric.mem_closedBall.mp hball
      rw [hrad] at hdist
      linarith
    change (Metric.closedBall (0 : E₈) R).indicator
      (fun y : E₈ => Real.exp (-‖y -
        a • EuclideanSpace.single (0 : Fin 8) (1 : ℝ)‖ ^ 2 / 2))
      ((p.2 : ℝ) • (p.1 : E₈)) = 0
    simp [Set.indicator, hout]
  exact hlocal.integrable_of_forall_notMem_eq_zero hzero

/-- A shifted Gaussian ball integral in E₈, decomposed into the actual S⁷
`toSphere` measure and the eighth-dimensional radial measure. -/
theorem eightDShiftedGaussianBallIntegral_eq_radiusSphereIntegral
    (a R : ℝ) (hR : 0 ≤ R) :
    (∫ y : E₈, (Metric.closedBall (0 : E₈) R).indicator
        (fun y => Real.exp (-‖y -
          a • EuclideanSpace.single (0 : Fin 8) (1 : ℝ)‖ ^ 2 / 2)) y
        ∂(volume : Measure E₈)) =
      ∫ r : Ioi (0 : ℝ),
        ∫ u : S₈,
          (Metric.closedBall (0 : E₈) R).indicator
            (fun y => Real.exp (-‖y -
              a • EuclideanSpace.single (0 : Fin 8) (1 : ℝ)‖ ^ 2 / 2))
            ((r : ℝ) • (u : E₈))
          ∂((volume : Measure E₈).toSphere)
        ∂(Measure.volumeIoiPow 7) := by
  let μS := (volume : Measure E₈).toSphere
  let μR := Measure.volumeIoiPow 7
  let f : S₈ × Ioi (0 : ℝ) → ℝ := fun p =>
    (Metric.closedBall (0 : E₈) R).indicator
      (fun y => Real.exp (-‖y -
        a • EuclideanSpace.single (0 : Fin 8) (1 : ℝ)‖ ^ 2 / 2))
      ((p.2 : ℝ) • (p.1 : E₈))
  have hpolar :
      (∫ y : E₈, (Metric.closedBall (0 : E₈) R).indicator
          (fun y => Real.exp (-‖y -
            a • EuclideanSpace.single (0 : Fin 8) (1 : ℝ)‖ ^ 2 / 2)) y
          ∂(volume : Measure E₈)) = ∫ p, f p ∂(μS.prod μR) := by
    simpa [f, μS, μR] using integral_euclidean_polarProduct
      (f := fun y : E₈ =>
        (Metric.closedBall (0 : E₈) R).indicator
          (fun y => Real.exp (-‖y -
            a • EuclideanSpace.single (0 : Fin 8) (1 : ℝ)‖ ^ 2 / 2)) y)
  have hInt : Integrable (Function.uncurry (fun u r => f (u, r))) (μS.prod μR) := by
    have hpair : Integrable (fun p => f p) (μS.prod μR) := by
      simpa [f, μS, μR] using integrable_eightDShiftedGaussianBallPolarIntegrand a R hR
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

/-- The centered ball indicator on a positive-radius S⁷ shell is exactly the
cutoff `r ≤ R`. -/
theorem eightDShiftedGaussianBallSphereSlice_eq
    (a r R : ℝ) (hr : 0 < r) :
    (∫ u : S₈,
      (Metric.closedBall (0 : E₈) R).indicator
        (fun y => Real.exp (-‖y -
          a • EuclideanSpace.single (0 : Fin 8) (1 : ℝ)‖ ^ 2 / 2))
        (r • (u : E₈))
      ∂((volume : Measure E₈).toSphere)) =
      if r ≤ R then
        ∫ u : S₈,
          Real.exp (-‖r • (u : E₈) -
            a • EuclideanSpace.single (0 : Fin 8) (1 : ℝ)‖ ^ 2 / 2)
          ∂((volume : Measure E₈).toSphere)
      else 0 := by
  have hu (u : S₈) : ‖(u : E₈)‖ = 1 := by
    simpa [dist_eq_norm] using u.property
  have hrad (u : S₈) : dist (r • (u : E₈)) 0 = r := by
    rw [dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
      hu u, mul_one]
  have hmem (u : S₈) : r • (u : E₈) ∈ Metric.closedBall (0 : E₈) R ↔ r ≤ R := by
    rw [Metric.mem_closedBall, hrad u]
  by_cases hcut : r ≤ R
  · have hpoint (u : S₈) :
        (Metric.closedBall (0 : E₈) R).indicator
          (fun y => Real.exp (-‖y -
            a • EuclideanSpace.single (0 : Fin 8) (1 : ℝ)‖ ^ 2 / 2))
          (r • (u : E₈)) =
        Real.exp (-‖r • (u : E₈) -
          a • EuclideanSpace.single (0 : Fin 8) (1 : ℝ)‖ ^ 2 / 2) := by
      simp [Set.indicator, hmem u, hcut]
    simp only [if_pos hcut]
    apply integral_congr_ae
    filter_upwards with u
    exact hpoint u
  · have hpoint (u : S₈) :
        (Metric.closedBall (0 : E₈) R).indicator
          (fun y => Real.exp (-‖y -
            a • EuclideanSpace.single (0 : Fin 8) (1 : ℝ)‖ ^ 2 / 2))
          (r • (u : E₈)) = 0 := by
      simp [Set.indicator, hmem u, hcut]
    simp only [if_neg hcut]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
    simp

/-- The positive-radius cutoff integral is the usual real interval mass on
`(0,R]`. -/
theorem integral_eightRadialKernelCutoff_eq_Ioc (a R : ℝ) :
    (∫ r : Ioi (0 : ℝ),
      if (r : ℝ) ≤ R then noncentralChiEvenRadialKernel 3 a r else 0
      ∂(Measure.comap Subtype.val (volume : Measure ℝ))) =
      ∫ r in Ioc (0 : ℝ) R, noncentralChiEvenRadialKernel 3 a r := by
  let k : ℝ → ℝ := noncentralChiEvenRadialKernel 3 a
  have hpoint (r : Ioi (0 : ℝ)) :
      (if (r : ℝ) ≤ R then k r else 0) =
        (Ioc (0 : ℝ) R).indicator k (r : ℝ) := by
    by_cases hr : (r : ℝ) ≤ R
    · rw [if_pos hr, Set.indicator_of_mem (mem_Ioc.mpr ⟨r.property, hr⟩)]
    · have hnot : (r : ℝ) ∉ Ioc (0 : ℝ) R := by
        intro h
        exact hr h.2
      rw [if_neg hr, Set.indicator_of_notMem hnot]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  rw [integral_subtype_comap measurableSet_Ioi]
  have hsubset : Ioc (0 : ℝ) R ⊆ Ioi (0 : ℝ) := by
    intro r hr
    exact hr.1
  have hindicator :
      (Ioi (0 : ℝ)).indicator ((Ioc (0 : ℝ) R).indicator k) =
        (Ioc (0 : ℝ) R).indicator k := by
    funext r
    by_cases hr : r ∈ Ioc (0 : ℝ) R
    · simp [hr, hsubset hr]
    · simp [hr]
  calc
    (∫ r in Ioi (0 : ℝ), (Ioc (0 : ℝ) R).indicator k r) =
        ∫ r, (Ioi (0 : ℝ)).indicator ((Ioc (0 : ℝ) R).indicator k) r := by
      rw [← integral_indicator measurableSet_Ioi]
    _ = ∫ r, (Ioc (0 : ℝ) R).indicator k r := by rw [hindicator]
    _ = ∫ r in Ioc (0 : ℝ) R, k r := integral_indicator measurableSet_Ioc

/-- The actual axial E₈ Gaussian ball integral, with standard normalizer, is
the lower-radius mass of the derived order-three factorial-series kernel. This
is an eight-dimensional real-model CDF bridge; it does not yet assert the
corresponding theorem for the repository's `ComplexSample` representation. -/
theorem stdGaussianEightDBall_axial_eq_radialCDF
    (a R : ℝ) (hR : 0 ≤ R) :
    (2 * Real.pi)⁻¹ ^ 4 *
      (∫ y : E₈,
        (Metric.closedBall (0 : E₈) R).indicator
          (fun y => Real.exp (-‖y -
            a • EuclideanSpace.single (0 : Fin 8) (1 : ℝ)‖ ^ 2 / 2)) y
        ∂(volume : Measure E₈)) =
      ∫ r in Ioc (0 : ℝ) R, noncentralChiEvenRadialKernel 3 a r := by
  let c : ℝ := (2 * Real.pi)⁻¹ ^ 4
  let g : Ioi (0 : ℝ) → ℝ := fun r =>
    ∫ u : S₈,
      (Metric.closedBall (0 : E₈) R).indicator
        (fun y => Real.exp (-‖y -
          a • EuclideanSpace.single (0 : Fin 8) (1 : ℝ)‖ ^ 2 / 2))
        ((r : ℝ) • (u : E₈))
      ∂((volume : Measure E₈).toSphere)
  have hpolar := eightDShiftedGaussianBallIntegral_eq_radiusSphereIntegral a R hR
  have hshell (r : Ioi (0 : ℝ)) :
      g r = if (r : ℝ) ≤ R then
        ∫ u : S₈,
          Real.exp (-‖(r : ℝ) • (u : E₈) -
            a • EuclideanSpace.single (0 : Fin 8) (1 : ℝ)‖ ^ 2 / 2)
          ∂((volume : Measure E₈).toSphere)
      else 0 := by
    simpa [g] using eightDShiftedGaussianBallSphereSlice_eq
      a (r : ℝ) R r.property
  calc
    _ = c * (∫ r : Ioi (0 : ℝ), g r ∂(Measure.volumeIoiPow 7)) := by
      rw [hpolar]
    _ = ∫ r : Ioi (0 : ℝ), c * g r ∂(Measure.volumeIoiPow 7) := by
      rw [← integral_const_mul]
    _ = ∫ r : Ioi (0 : ℝ),
          (r : ℝ) ^ 7 * (c * g r)
          ∂(Measure.comap Subtype.val (volume : Measure ℝ)) := by
      rw [integral_volumeIoiPow_seven_eq_Ioi]
    _ = ∫ r : Ioi (0 : ℝ),
          (if (r : ℝ) ≤ R then noncentralChiEvenRadialKernel 3 a r else 0)
          ∂(Measure.comap Subtype.val (volume : Measure ℝ)) := by
      apply integral_congr_ae
      filter_upwards with r
      rw [hshell r]
      by_cases hcut : (r : ℝ) ≤ R
      · simp only [if_pos hcut]
        calc
          (r : ℝ) ^ 7 * (c *
              ∫ u : S₈,
                Real.exp (-‖(r : ℝ) • (u : E₈) -
                  a • EuclideanSpace.single (0 : Fin 8) (1 : ℝ)‖ ^ 2 / 2)
                ∂((volume : Measure E₈).toSphere)) =
              (2 * Real.pi)⁻¹ ^ 4 * (r : ℝ) ^ 7 *
                (∫ u : S₈,
                  Real.exp (-‖(r : ℝ) • (u : E₈) -
                    a • EuclideanSpace.single (0 : Fin 8) (1 : ℝ)‖ ^ 2 / 2)
                  ∂((volume : Measure E₈).toSphere)) := by
            dsimp [c]
            ring
          _ = noncentralChiEvenRadialKernel 3 a r :=
            eightDShiftedGaussianShell_eq_radialKernel a (r : ℝ)
      · simp [hcut]
    _ = ∫ r in Ioc (0 : ℝ) R, noncentralChiEvenRadialKernel 3 a r :=
      integral_eightRadialKernelCutoff_eq_Ioc a R


end

end JinWishart

