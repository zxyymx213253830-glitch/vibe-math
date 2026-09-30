import JinWishartFormalization.NoncentralOneColumnEnergy
import JinWishartFormalization.FourDimensionalPolarBridge
import JinWishartFormalization.SphereSixDAxialMeasure
import JinWishartFormalization.SixDimensionalAngularBesselI2
import JinWishartFormalization.NuttallQ21Normalization
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Axial six-dimensional noncentral Gaussian shell

This module connects the already formalized S⁵ angular measure identity to
the radial kernel of an axially shifted six-dimensional real Gaussian.  It
proves a Bessel-free factorial-series shell formula.  The actual complex
`3 × 1` sample-to-`E₆` isometry, the radius-polar ball integral, and the
order-two modified-Bessel/Nuttall-Q tail normalization are deliberately kept
as separate obligations.
-/

open MeasureTheory Set

namespace JinWishart

noncomputable section

local notation "E₆" => EuclideanSpace ℝ (Fin 6)
local notation "S₆" => Metric.sphere (0 : E₆) 1

/-- Angular chart factor for an axial exponential on S⁵, using the actual
`toSphere` measure normalization. -/
def sixDSphereExpAngleIntegralChart (κ : ℝ) : ℝ :=
  (8 * Real.pi ^ 2 / 3) *
    ∫ θ in (0 : ℝ)..Real.pi,
      Real.sin θ ^ 4 * Real.exp (κ * Real.cos θ)

/-- The actual S⁵ `toSphere` exponential integral is the normalized
one-angle chart factor. -/
theorem sixDSphereToSphereIntegral_eq_angleChart (κ : ℝ) :
    (∫ u : S₆, Real.exp (κ * (u : E₆) 0)
      ∂((volume : Measure E₆).toSphere)) =
      sixDSphereExpAngleIntegralChart κ := by
  exact sphereSixToSphereExpIntegral_eq_angleChart κ

/-- Squared distance from a polar point to a center on the first coordinate
axis, in six real dimensions. -/
theorem sixDDistance_sq_sub_firstAxis (u : S₆) (r a : ℝ) :
    ‖r • (u : E₆) - a • EuclideanSpace.single (0 : Fin 6) (1 : ℝ)‖ ^ 2 =
      r ^ 2 + a ^ 2 - 2 * a * r * (u : E₆) 0 := by
  have hu : ‖(u : E₆)‖ = 1 := by
    simpa [dist_eq_norm] using u.property
  rw [norm_sub_sq_real, norm_smul, norm_smul, hu]
  rw [real_inner_smul_left, real_inner_smul_right]
  simp [Real.norm_eq_abs, EuclideanSpace.inner_single_right]
  ring_nf

/-- The S⁵ angular integral for a shifted Gaussian shell factors into its
radial Gaussian exponential and the exact exponential chart factor. -/
theorem sixDShiftedGaussianAngularIntegral_eq_chart (a r : ℝ) :
    (∫ u : S₆,
      Real.exp (-‖r • (u : E₆) -
        a • EuclideanSpace.single (0 : Fin 6) (1 : ℝ)‖ ^ 2 / 2)
      ∂((volume : Measure E₆).toSphere)) =
      Real.exp (-((r ^ 2 + a ^ 2) / 2)) *
        sixDSphereExpAngleIntegralChart (a * r) := by
  calc
    _ = ∫ u : S₆,
        Real.exp (-((r ^ 2 + a ^ 2) / 2)) *
          Real.exp (a * r * (u : E₆) 0)
        ∂((volume : Measure E₆).toSphere) := by
      apply integral_congr_ae
      filter_upwards with u
      rw [sixDDistance_sq_sub_firstAxis]
      have he : -(r ^ 2 + a ^ 2 - 2 * a * r *
          (u : E₆) 0) / 2 =
          -((r ^ 2 + a ^ 2) / 2) + a * r * (u : E₆) 0 := by ring
      rw [he, Real.exp_add]
    _ = Real.exp (-((r ^ 2 + a ^ 2) / 2)) *
        (∫ u : S₆, Real.exp (a * r * (u : E₆) 0)
          ∂((volume : Measure E₆).toSphere)) := by
      rw [integral_const_mul]
    _ = Real.exp (-((r ^ 2 + a ^ 2) / 2)) *
        sixDSphereExpAngleIntegralChart (a * r) := by
      rw [sixDSphereToSphereIntegral_eq_angleChart]

/-- Bessel-free six-dimensional noncentral radial density kernel. The power
series is the exact order-two modified-Bessel series, but is kept explicit so
the geometric shell theorem does not depend on an unproved special-function
identification. -/
def noncentralChiSixRadialSeriesKernel (a r : ℝ) : ℝ :=
  (r ^ 5 / 4) * Real.exp (-((r ^ 2 + a ^ 2) / 2)) *
    ∑' n : ℕ,
      ((a * r) ^ 2 / 4) ^ n /
        ((n.factorial : ℝ) * ((n + 2).factorial : ℝ))

/-- The six-dimensional factorial-series radial kernel is nonnegative at
nonnegative radii. -/
theorem noncentralChiSixRadialSeriesKernel_nonneg
    (a r : ℝ) (hr : 0 ≤ r) :
    0 ≤ noncentralChiSixRadialSeriesKernel a r := by
  unfold noncentralChiSixRadialSeriesKernel
  apply mul_nonneg
  · apply mul_nonneg
    · positivity
    · exact Real.exp_nonneg _
  · apply tsum_nonneg
    intro n
    positivity

/-- The radial law depends only on the magnitude of the axial displacement. -/
@[simp] theorem noncentralChiSixRadialSeriesKernel_abs (a r : ℝ) :
    noncentralChiSixRadialSeriesKernel |a| r =
      noncentralChiSixRadialSeriesKernel a r := by
  unfold noncentralChiSixRadialSeriesKernel
  have ha : |a| ^ 2 = a ^ 2 := sq_abs a
  have har : (|a| * r) ^ 2 = (a * r) ^ 2 := by
    calc
      (|a| * r) ^ 2 = |a| ^ 2 * r ^ 2 := by rw [mul_pow]
      _ = a ^ 2 * r ^ 2 := by rw [sq_abs]
      _ = (a * r) ^ 2 := by rw [mul_pow]
  rw [ha, har]

/-- At zero noncentrality, only the zeroth I₂-series term remains, giving the
central six-dimensional chi radial density. -/
theorem noncentralChiSixRadialSeriesKernel_zero (r : ℝ) :
    noncentralChiSixRadialSeriesKernel 0 r =
      (r ^ 5 / 8) * Real.exp (-(r ^ 2 / 2)) := by
  unfold noncentralChiSixRadialSeriesKernel
  have hseries :
      (∑' n : ℕ,
        ((0 * r) ^ 2 / 4) ^ n /
          ((n.factorial : ℝ) * ((n + 2).factorial : ℝ))) = 1 / 2 := by
    have hterm (n : ℕ) :
        ((0 * r) ^ 2 / 4) ^ n /
          ((n.factorial : ℝ) * ((n + 2).factorial : ℝ)) =
          if n = 0 then (1 / 2 : ℝ) else 0 := by
      cases n with
      | zero => simp
      | succ n => simp
    simp_rw [hterm]
    simp
  rw [hseries]
  ring

/-- The central six-dimensional radial-series kernel has total mass one.
The case `a=0` is handled directly by the sixth Gaussian moment, without any
division by the noncentrality amplitude. -/
theorem noncentralChiSixRadialSeriesKernel_zero_integral_eq_one :
    (∫ r in Ioi (0 : ℝ), noncentralChiSixRadialSeriesKernel 0 r) = 1 := by
  rw [show (fun r : ℝ => noncentralChiSixRadialSeriesKernel 0 r) =
      fun r => (r ^ 5 / 8) * Real.exp (-(r ^ 2 / 2)) by
        funext r
        exact noncentralChiSixRadialSeriesKernel_zero r]
  have hfun : (fun r : ℝ => (r ^ 5 / 8) * Real.exp (-(r ^ 2 / 2))) =
      fun r => (1 / 8 : ℝ) * (r ^ 5 * Real.exp (-(r ^ 2 / 2))) := by
    funext r
    ring
  rw [hfun, integral_const_mul]
  rw [gaussianOddMoment 1]
  norm_num

/-- Exact shell identity: the six-dimensional Gaussian density normalizer,
the S⁵ surface measure, and the radial Jacobian together give the
order-two factorial-series kernel. -/
theorem sixDShiftedGaussianShell_eq_seriesKernel (a r : ℝ) :
    (2 * Real.pi)⁻¹ ^ 3 * r ^ 5 *
      (∫ u : S₆,
        Real.exp (-‖r • (u : E₆) -
          a • EuclideanSpace.single (0 : Fin 6) (1 : ℝ)‖ ^ 2 / 2)
        ∂((volume : Measure E₆).toSphere)) =
      noncentralChiSixRadialSeriesKernel a r := by
  rw [sixDShiftedGaussianAngularIntegral_eq_chart,
    sixDSphereExpAngleIntegralChart,
    angularSinFourIntegral_eq_besselI2Series]
  unfold noncentralChiSixRadialSeriesKernel
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hpi]
  <;> ring

/-- Unfolding the sixth-dimensional radial measure gives the usual r⁵
Jacobian on positive radii. -/
theorem integral_volumeIoiPow_five_eq_Ioi (f : Ioi (0 : ℝ) → ℝ) :
    (∫ r, f r ∂(Measure.volumeIoiPow 5)) =
      ∫ r : Ioi (0 : ℝ), (r : ℝ) ^ 5 * f r
        ∂(Measure.comap Subtype.val (volume : Measure ℝ)) := by
  rw [Measure.volumeIoiPow, integral_withDensity_eq_integral_toReal_smul]
  · congr 1
    funext r
    have hr : 0 < (r : ℝ) := r.property
    simp only [ENNReal.toReal_ofReal (pow_nonneg hr.le 5)]
    simp [smul_eq_mul]
  · fun_prop
  · filter_upwards with r
    simp

/-- The centered-ball cutoff is integrable on the S⁵/radius product: the
radius is confined to a bounded interval and the Gaussian factor is at most
one. -/
theorem integrable_sixDShiftedGaussianBallPolarIntegrand
    (a R : ℝ) (hR : 0 ≤ R) :
    Integrable
      (fun p : S₆ × Ioi (0 : ℝ) =>
        (Metric.closedBall (0 : E₆) R).indicator
          (fun y : E₆ => Real.exp (-‖y -
            a • EuclideanSpace.single (0 : Fin 6) (1 : ℝ)‖ ^ 2 / 2))
          ((p.2 : ℝ) • (p.1 : E₆)))
      (((volume : Measure E₆).toSphere).prod (Measure.volumeIoiPow 5)) := by
  classical
  let f : S₆ × Ioi (0 : ℝ) → ℝ := fun p =>
    (Metric.closedBall (0 : E₆) R).indicator
      (fun y : E₆ => Real.exp (-‖y -
        a • EuclideanSpace.single (0 : Fin 6) (1 : ℝ)‖ ^ 2 / 2))
      ((p.2 : ℝ) • (p.1 : E₆))
  let ρ : Ioi (0 : ℝ) := ⟨R + 1,
    add_pos_of_nonneg_of_pos hR (by norm_num : (0 : ℝ) < 1)⟩
  let K : Set (S₆ × Ioi (0 : ℝ)) := Set.univ ×ˢ Set.Iio ρ
  have hmeas : Measurable f := by
    have hbody : Measurable (fun y : E₆ => Real.exp (-‖y -
        a • EuclideanSpace.single (0 : Fin 6) (1 : ℝ)‖ ^ 2 / 2)) := by fun_prop
    have hcut : Measurable ((Metric.closedBall (0 : E₆) R).indicator
        (fun y : E₆ => Real.exp (-‖y -
          a • EuclideanSpace.single (0 : Fin 6) (1 : ℝ)‖ ^ 2 / 2))) :=
      hbody.indicator measurableSet_closedBall
    dsimp [f]
    exact hcut.comp (by fun_prop)
  have hbound (p : S₆ × Ioi (0 : ℝ)) : ‖f p‖ ≤ 1 := by
    dsimp [f]
    rw [Set.indicator_apply]
    split_ifs with hp
    · rw [abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_one_iff.mpr
      nlinarith [sq_nonneg (‖((p.2 : ℝ) • (p.1 : E₆)) -
        a • EuclideanSpace.single (0 : Fin 6) (1 : ℝ)‖)]
    · simp
  have hsphere : ((volume : Measure E₆).toSphere) Set.univ ≠ ⊤ :=
    ne_of_lt (measure_lt_top _ _)
  have hradius : (Measure.volumeIoiPow 5) (Set.Iio ρ) ≠ ⊤ := by
    rw [Measure.volumeIoiPow_apply_Iio]
    exact ENNReal.ofReal_ne_top
  have hKfinite :
      ((((volume : Measure E₆).toSphere).prod (Measure.volumeIoiPow 5)) K) ≠ ⊤ := by
    change ((((volume : Measure E₆).toSphere).prod (Measure.volumeIoiPow 5))
      (Set.univ ×ˢ Set.Iio ρ)) ≠ ⊤
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top hsphere hradius
  have hboundAE : ∀ᵐ p ∂((((volume : Measure E₆).toSphere).prod
      (Measure.volumeIoiPow 5)).restrict K), ‖f p‖ ≤ 1 :=
    Filter.Eventually.of_forall hbound
  have hlocal : IntegrableOn f K
      (((volume : Measure E₆).toSphere).prod (Measure.volumeIoiPow 5)) :=
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
    have hu : ‖(p.1 : E₆)‖ = 1 := by
      simpa [dist_eq_norm] using p.1.property
    have hrad : ‖(p.2 : ℝ) • (p.1 : E₆)‖ = (p.2 : ℝ) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos p.2.property, hu, mul_one]
    have hout : ((p.2 : ℝ) • (p.1 : E₆)) ∉ Metric.closedBall (0 : E₆) R := by
      intro hball
      have hdist : ‖(p.2 : ℝ) • (p.1 : E₆)‖ ≤ R := by
        simpa [dist_eq_norm] using Metric.mem_closedBall.mp hball
      rw [hrad] at hdist
      linarith
    change (Metric.closedBall (0 : E₆) R).indicator
      (fun y : E₆ => Real.exp (-‖y -
        a • EuclideanSpace.single (0 : Fin 6) (1 : ℝ)‖ ^ 2 / 2))
      ((p.2 : ℝ) • (p.1 : E₆)) = 0
    simp [Set.indicator, hout]
  exact hlocal.integrable_of_forall_notMem_eq_zero hzero

/-- A shifted Gaussian ball integral in E₆, decomposed into the actual S⁵
`toSphere` measure and the sixth-dimensional radial measure. -/
theorem sixDShiftedGaussianBallIntegral_eq_radiusSphereIntegral
    (a R : ℝ) (hR : 0 ≤ R) :
    (∫ y : E₆, (Metric.closedBall (0 : E₆) R).indicator
        (fun y => Real.exp (-‖y -
          a • EuclideanSpace.single (0 : Fin 6) (1 : ℝ)‖ ^ 2 / 2)) y
        ∂(volume : Measure E₆)) =
      ∫ r : Ioi (0 : ℝ),
        ∫ u : S₆,
          (Metric.closedBall (0 : E₆) R).indicator
            (fun y => Real.exp (-‖y -
              a • EuclideanSpace.single (0 : Fin 6) (1 : ℝ)‖ ^ 2 / 2))
            ((r : ℝ) • (u : E₆))
          ∂((volume : Measure E₆).toSphere)
        ∂(Measure.volumeIoiPow 5) := by
  let μS := (volume : Measure E₆).toSphere
  let μR := Measure.volumeIoiPow 5
  let f : S₆ × Ioi (0 : ℝ) → ℝ := fun p =>
    (Metric.closedBall (0 : E₆) R).indicator
      (fun y => Real.exp (-‖y -
        a • EuclideanSpace.single (0 : Fin 6) (1 : ℝ)‖ ^ 2 / 2))
      ((p.2 : ℝ) • (p.1 : E₆))
  have hpolar :
      (∫ y : E₆, (Metric.closedBall (0 : E₆) R).indicator
          (fun y => Real.exp (-‖y -
            a • EuclideanSpace.single (0 : Fin 6) (1 : ℝ)‖ ^ 2 / 2)) y
          ∂(volume : Measure E₆)) = ∫ p, f p ∂(μS.prod μR) := by
    simpa [f, μS, μR] using integral_euclidean_polarProduct
      (f := fun y : E₆ =>
        (Metric.closedBall (0 : E₆) R).indicator
          (fun y => Real.exp (-‖y -
            a • EuclideanSpace.single (0 : Fin 6) (1 : ℝ)‖ ^ 2 / 2)) y)
  have hInt : Integrable (Function.uncurry (fun u r => f (u, r))) (μS.prod μR) := by
    have hpair : Integrable (fun p => f p) (μS.prod μR) := by
      simpa [f, μS, μR] using integrable_sixDShiftedGaussianBallPolarIntegrand a R hR
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

/-- The centered ball indicator on a positive-radius S⁵ shell is exactly the
cutoff `r ≤ R`. -/
theorem sixDShiftedGaussianBallSphereSlice_eq
    (a r R : ℝ) (hr : 0 < r) :
    (∫ u : S₆,
      (Metric.closedBall (0 : E₆) R).indicator
        (fun y => Real.exp (-‖y -
          a • EuclideanSpace.single (0 : Fin 6) (1 : ℝ)‖ ^ 2 / 2))
        (r • (u : E₆))
      ∂((volume : Measure E₆).toSphere)) =
      if r ≤ R then
        ∫ u : S₆,
          Real.exp (-‖r • (u : E₆) -
            a • EuclideanSpace.single (0 : Fin 6) (1 : ℝ)‖ ^ 2 / 2)
          ∂((volume : Measure E₆).toSphere)
      else 0 := by
  have hu (u : S₆) : ‖(u : E₆)‖ = 1 := by
    simpa [dist_eq_norm] using u.property
  have hrad (u : S₆) : dist (r • (u : E₆)) 0 = r := by
    rw [dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
      hu u, mul_one]
  have hmem (u : S₆) : r • (u : E₆) ∈ Metric.closedBall (0 : E₆) R ↔ r ≤ R := by
    rw [Metric.mem_closedBall, hrad u]
  by_cases hcut : r ≤ R
  · have hpoint (u : S₆) :
        (Metric.closedBall (0 : E₆) R).indicator
          (fun y => Real.exp (-‖y -
            a • EuclideanSpace.single (0 : Fin 6) (1 : ℝ)‖ ^ 2 / 2))
          (r • (u : E₆)) =
        Real.exp (-‖r • (u : E₆) -
          a • EuclideanSpace.single (0 : Fin 6) (1 : ℝ)‖ ^ 2 / 2) := by
      simp [Set.indicator, hmem u, hcut]
    simp only [if_pos hcut]
    apply integral_congr_ae
    filter_upwards with u
    exact hpoint u
  · have hpoint (u : S₆) :
        (Metric.closedBall (0 : E₆) R).indicator
          (fun y => Real.exp (-‖y -
            a • EuclideanSpace.single (0 : Fin 6) (1 : ℝ)‖ ^ 2 / 2))
          (r • (u : E₆)) = 0 := by
      simp [Set.indicator, hmem u, hcut]
    simp only [if_neg hcut]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
    simp

/-- The positive-radius cutoff integral is the usual real interval mass on
`(0,R]`. -/
theorem integral_sixRadialKernelCutoff_eq_Ioc (a R : ℝ) :
    (∫ r : Ioi (0 : ℝ),
      if (r : ℝ) ≤ R then noncentralChiSixRadialSeriesKernel a r else 0
      ∂(Measure.comap Subtype.val (volume : Measure ℝ))) =
      ∫ r in Ioc (0 : ℝ) R, noncentralChiSixRadialSeriesKernel a r := by
  let k : ℝ → ℝ := noncentralChiSixRadialSeriesKernel a
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

/-- The actual axial E₆ Gaussian ball integral, with standard normalizer, is
the lower-radius mass of the derived order-two factorial-series kernel. This
is a six-dimensional real-model CDF bridge; it does not yet assert the
corresponding theorem for the repository's `ComplexSample` representation. -/
theorem stdGaussianSixDBall_axial_eq_radialSeriesCDF
    (a R : ℝ) (hR : 0 ≤ R) :
    (2 * Real.pi)⁻¹ ^ 3 *
      (∫ y : E₆,
        (Metric.closedBall (0 : E₆) R).indicator
          (fun y => Real.exp (-‖y -
            a • EuclideanSpace.single (0 : Fin 6) (1 : ℝ)‖ ^ 2 / 2)) y
        ∂(volume : Measure E₆)) =
      ∫ r in Ioc (0 : ℝ) R, noncentralChiSixRadialSeriesKernel a r := by
  let c : ℝ := (2 * Real.pi)⁻¹ ^ 3
  let g : Ioi (0 : ℝ) → ℝ := fun r =>
    ∫ u : S₆,
      (Metric.closedBall (0 : E₆) R).indicator
        (fun y => Real.exp (-‖y -
          a • EuclideanSpace.single (0 : Fin 6) (1 : ℝ)‖ ^ 2 / 2))
        ((r : ℝ) • (u : E₆))
      ∂((volume : Measure E₆).toSphere)
  have hpolar := sixDShiftedGaussianBallIntegral_eq_radiusSphereIntegral a R hR
  have hshell (r : Ioi (0 : ℝ)) :
      g r = if (r : ℝ) ≤ R then
        ∫ u : S₆,
          Real.exp (-‖(r : ℝ) • (u : E₆) -
            a • EuclideanSpace.single (0 : Fin 6) (1 : ℝ)‖ ^ 2 / 2)
          ∂((volume : Measure E₆).toSphere)
      else 0 := by
    simpa [g] using sixDShiftedGaussianBallSphereSlice_eq
      a (r : ℝ) R r.property
  calc
    _ = c * (∫ r : Ioi (0 : ℝ), g r ∂(Measure.volumeIoiPow 5)) := by
      rw [hpolar]
    _ = ∫ r : Ioi (0 : ℝ), c * g r ∂(Measure.volumeIoiPow 5) := by
      rw [← integral_const_mul]
    _ = ∫ r : Ioi (0 : ℝ),
          (r : ℝ) ^ 5 * (c * g r)
          ∂(Measure.comap Subtype.val (volume : Measure ℝ)) := by
      rw [integral_volumeIoiPow_five_eq_Ioi]
    _ = ∫ r : Ioi (0 : ℝ),
          (if (r : ℝ) ≤ R then noncentralChiSixRadialSeriesKernel a r else 0)
          ∂(Measure.comap Subtype.val (volume : Measure ℝ)) := by
      apply integral_congr_ae
      filter_upwards with r
      rw [hshell r]
      by_cases hcut : (r : ℝ) ≤ R
      · simp only [if_pos hcut]
        calc
          (r : ℝ) ^ 5 * (c *
              ∫ u : S₆,
                Real.exp (-‖(r : ℝ) • (u : E₆) -
                  a • EuclideanSpace.single (0 : Fin 6) (1 : ℝ)‖ ^ 2 / 2)
                ∂((volume : Measure E₆).toSphere)) =
              (2 * Real.pi)⁻¹ ^ 3 * (r : ℝ) ^ 5 *
                (∫ u : S₆,
                  Real.exp (-‖(r : ℝ) • (u : E₆) -
                    a • EuclideanSpace.single (0 : Fin 6) (1 : ℝ)‖ ^ 2 / 2)
                  ∂((volume : Measure E₆).toSphere)) := by
            dsimp [c]
            ring
          _ = noncentralChiSixRadialSeriesKernel a r :=
            sixDShiftedGaussianShell_eq_seriesKernel a (r : ℝ)
      · simp [hcut]
    _ = ∫ r in Ioc (0 : ℝ) R, noncentralChiSixRadialSeriesKernel a r :=
      integral_sixRadialKernelCutoff_eq_Ioc a R

/-- The order-two modified Bessel function is the regularized `₀F₁` with
parameter three, including the quadratic leading factor. -/
theorem modifiedBesselI_two_eq_regularizedHG (z : ℂ) :
    modifiedBesselI 2 z = (z / 2) ^ 2 *
      Complex.regularizedHGFun 0 {3} (z ^ 2 / 4) := by
  simp only [modifiedBesselI, Complex.besselJ_def]
  norm_num
  simp only [div_eq_mul_inv, mul_pow, Complex.I_sq, inv_pow]
  field_simp
  simp [Complex.I_sq]
  norm_num

/-- The regularized hypergeometric coefficient at parameter three is the
factorial coefficient required by the order-two Bessel series. -/
theorem regularizedHGFunCoeff_zero_singleton_three (n : ℕ) :
    Complex.regularizedHGFunCoeff 0 {3} n =
      (((n.factorial : ℂ) * ((n + 2).factorial : ℂ))⁻¹) := by
  simp only [Complex.regularizedHGFunCoeff, Multiset.map_zero, Multiset.prod_zero,
    Multiset.map_singleton, Multiset.prod_singleton]
  have harg : (3 : ℂ) + (n : ℂ) = ((n + 2 : ℕ) : ℂ) + 1 := by
    push_cast
    ring
  rw [harg, Complex.Gamma_nat_eq_factorial]
  push_cast
  simp only [Nat.factorial]
  field_simp

/-- The regularized hypergeometric function with parameter three is its
coefficient power series. -/
theorem regularizedHGFun_zero_singleton_three_eq_tsum (z : ℂ) :
    Complex.regularizedHGFun 0 {3} z =
      ∑' n : ℕ, Complex.regularizedHGFunCoeff 0 {3} n * z ^ n := by
  rw [Complex.regularizedHGFun, Complex.regularizedHGFunSeries]
  change FormalMultilinearSeries.ofScalarsSum
    (Complex.regularizedHGFunCoeff 0 {3}) z = _
  rw [FormalMultilinearSeries.ofScalars_sum_eq]
  simp only [smul_eq_mul]

/-- Complex factorial-series expansion for the order-two modified Bessel
function. -/
theorem modifiedBesselI_two_eq_factorialSeries (z : ℂ) :
    modifiedBesselI 2 z = (z / 2) ^ 2 * ∑' n : ℕ,
      (z ^ 2 / 4) ^ n /
        ((n.factorial : ℂ) * ((n + 2).factorial : ℂ)) := by
  rw [modifiedBesselI_two_eq_regularizedHG,
    regularizedHGFun_zero_singleton_three_eq_tsum]
  congr 1
  apply tsum_congr
  intro n
  rw [regularizedHGFunCoeff_zero_singleton_three]
  push_cast
  ring

/-- For real inputs, the real order-two factorial series is exactly the
modified Bessel `I₂` used in the paper's Nuttall-Q integrand. -/
theorem besselI2RealSeries_eq_modifiedBesselI (x : ℝ) :
    (besselI2RealSeries x : ℂ) = modifiedBesselI 2 (x : ℂ) := by
  rw [besselI2RealSeries, Complex.ofReal_mul, Complex.ofReal_tsum,
    modifiedBesselI_two_eq_factorialSeries]
  have hlead : (((x ^ 2 / 4 : ℝ) : ℂ)) = ((x : ℂ) / 2) ^ 2 := by
    push_cast
    ring
  rw [hlead]
  apply congrArg (fun z : ℂ => ((x : ℂ) / 2) ^ 2 * z)
  apply tsum_congr
  intro n
  push_cast
  ring

/-- The Bessel-free shell kernel is precisely the `(p,q)=(3,2)` Nuttall
kernel divided by the squared noncentrality amplitude. -/
theorem noncentralChiSixRadialSeriesKernel_eq_nuttallQ32_div_sq
    (a r : ℝ) (ha : a ≠ 0) :
    (noncentralChiSixRadialSeriesKernel a r : ℂ) =
      nuttallQIntegrand 3 2 a r / (a : ℂ) ^ 2 := by
  rw [nuttallQIntegrand, ← besselI2RealSeries_eq_modifiedBesselI]
  unfold noncentralChiSixRadialSeriesKernel besselI2RealSeries
  push_cast
  field_simp [ha]
  <;> ring

/-- The radial-series kernel is measurable in the radius. For nonzero `a`,
this follows from its proved identification with the real part of the
continuous Nuttall integrand; at `a=0` use the explicit Gaussian formula. -/
theorem measurable_noncentralChiSixRadialSeriesKernel (a : ℝ) :
    Measurable (fun r : ℝ => noncentralChiSixRadialSeriesKernel a r) := by
  by_cases ha : a = 0
  · subst a
    have hfun : (fun r : ℝ => noncentralChiSixRadialSeriesKernel 0 r) =
        fun r => (r ^ 5 / 8) * Real.exp (-(r ^ 2 / 2)) := by
      funext r
      exact noncentralChiSixRadialSeriesKernel_zero r
    rw [hfun]
    fun_prop
  · have hfun : (fun r : ℝ => noncentralChiSixRadialSeriesKernel a r) =
        fun r => (nuttallQIntegrand 3 2 a r / (a : ℂ) ^ 2).re := by
      funext r
      have h := noncentralChiSixRadialSeriesKernel_eq_nuttallQ32_div_sq a r ha
      have hr := congrArg Complex.re h
      simpa using hr
    rw [hfun]
    fun_prop

/-- The order-two factorial series is bounded by the order-zero series,
because `(n+2)! ≥ n!`. -/
private theorem sixD_factorialSeries_le_besselI0Series (x : ℝ) :
    (∑' n : ℕ,
      ((x * x) / 4) ^ n /
      ((n.factorial : ℝ) * ((n + 2).factorial : ℝ))) ≤
      ∑' n : ℕ, ((x * x) / 4) ^ n / ((n.factorial : ℝ) ^ 2) := by
  have hz : 0 ≤ x * x / 4 := by
    apply div_nonneg
    · nlinarith [sq_nonneg x]
    · norm_num
  have hsum : Summable (fun n : ℕ => (x * x / 4) ^ n /
      ((n.factorial : ℝ) ^ 2)) := by
    apply (Real.summable_pow_div_factorial (x * x / 4)).of_norm_bounded
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg
      (div_nonneg (pow_nonneg hz n) (by positivity))]
    apply div_le_div_of_nonneg_left (pow_nonneg hz n) (by positivity)
    have hf : (1 : ℝ) ≤ (n.factorial : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt (Nat.factorial_pos n))
    nlinarith [sq_nonneg ((n.factorial : ℝ) - 1)]
  have hleft : Summable (fun n : ℕ => (x * x / 4) ^ n /
      ((n.factorial : ℝ) * ((n + 2).factorial : ℝ))) := by
    apply (Real.summable_pow_div_factorial (x * x / 4)).of_norm_bounded
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg
      (div_nonneg (pow_nonneg hz n) (by positivity))]
    apply div_le_div_of_nonneg_left (pow_nonneg hz n) (by positivity)
    have hfact2 : (1 : ℝ) ≤ ((n + 2).factorial : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt (Nat.factorial_pos (n + 2)))
    have hprod : 0 ≤ (n.factorial : ℝ) *
        (((n + 2).factorial : ℝ) - 1) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr hfact2)
    nlinarith
  apply Summable.tsum_le_tsum
    (fun n => ?_) hleft hsum
  ·
    apply div_le_div_of_nonneg_left (pow_nonneg hz n) (by positivity)
    have hfact : (n.factorial : ℝ) ≤ ((n + 2).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (show n ≤ n + 2 by omega)
    have hprod : 0 ≤ (n.factorial : ℝ) *
        (((n + 2).factorial : ℝ) - (n.factorial : ℝ)) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr hfact)
    nlinarith

/-- The order-zero factorial series is at most `exp |x|`, by its circle
integral representation and the pointwise bound `cos θ ≤ 1`. -/
private theorem sixD_besselI0Series_le_exp (x : ℝ) :
    (∑' n : ℕ, ((x * x) / 4) ^ n / ((n.factorial : ℝ) ^ 2)) ≤
      Real.exp |x| := by
  have hab : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hfcont : Continuous (fun θ : ℝ => Real.exp (|x| * Real.cos θ)) := by
    fun_prop
  have hf : IntervalIntegrable (fun θ : ℝ => Real.exp (|x| * Real.cos θ))
      volume 0 (2 * Real.pi) := hfcont.intervalIntegrable _ _
  have hgcont : Continuous (fun _ : ℝ => Real.exp |x|) := continuous_const
  have hg : IntervalIntegrable (fun _ : ℝ => Real.exp |x|)
      volume 0 (2 * Real.pi) := hgcont.intervalIntegrable _ _
  have hangle :
      (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.exp (|x| * Real.cos θ)) ≤
        ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.exp |x| := by
    apply intervalIntegral.integral_mono_on hab hf hg
    intro θ hθ
    apply Real.exp_le_exp.mpr
    calc
      |x| * Real.cos θ ≤ |x| * 1 :=
        mul_le_mul_of_nonneg_left (Real.cos_le_one θ) (abs_nonneg x)
      _ = |x| := by ring
  rw [angularExpIntegral_eq_factorialSeries |x|] at hangle
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hangle
  have hseries :
      (∑' n : ℕ, (|x| ^ 2 / 4) ^ n / ((n.factorial : ℝ) ^ 2)) =
        ∑' n : ℕ, (x * x / 4) ^ n / ((n.factorial : ℝ) ^ 2) := by
    apply tsum_congr
    intro n
    rw [sq_abs]
    rw [show x ^ 2 / 4 = x * x / 4 by ring]
  rw [hseries] at hangle
  have hpi : 0 < 2 * Real.pi := by positivity
  exact (le_of_mul_le_mul_left hangle hpi).trans_eq (by ring)

/-- For every real `x`, the order-two factorial series is bounded by
`exp |x|`. -/
private theorem sixD_factorialSeries_le_exp_abs (x : ℝ) :
    (∑' n : ℕ,
      ((x * x) / 4) ^ n /
        ((n.factorial : ℝ) * ((n + 2).factorial : ℝ))) ≤
      Real.exp |x| :=
  (sixD_factorialSeries_le_besselI0Series x).trans
    (sixD_besselI0Series_le_exp x)

/-- The six-dimensional radial kernel admits an integrable Gaussian-polynomial
majorant on positive radii, for every noncentrality parameter. -/
theorem integrableOn_noncentralChiSixRadialSeriesKernel (a : ℝ) :
    IntegrableOn (noncentralChiSixRadialSeriesKernel a) (Ioi (0 : ℝ)) := by
  have hbase : IntegrableOn
      (fun r : ℝ => r ^ 5 * Real.exp (-(1 / 4 : ℝ) * r ^ 2)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_sq
      (b := (1 / 4 : ℝ)) (s := (5 : ℝ)) (by norm_num) (by norm_num)
    apply (integrableOn_congr_fun (s := Ioi (0 : ℝ)) ?_ measurableSet_Ioi).2 h
    intro r hr
    change r ^ 5 * Real.exp (-(1 / 4 : ℝ) * r ^ 2) =
      Real.rpow r (5 : ℝ) * Real.exp (-(1 / 4 : ℝ) * r ^ 2)
    simp
  let C : ℝ := (Real.exp (a ^ 2 / 2)) / 4
  have hmajor : IntegrableOn
      (fun r : ℝ => C * (r ^ 5 * Real.exp (-(1 / 4 : ℝ) * r ^ 2)))
      (Ioi 0) := hbase.const_mul C
  have hmeas : AEStronglyMeasurable (noncentralChiSixRadialSeriesKernel a)
      (volume.restrict (Ioi 0)) :=
    (measurable_noncentralChiSixRadialSeriesKernel a).aestronglyMeasurable
  apply Integrable.mono' hmajor hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  rw [Real.norm_eq_abs, abs_of_nonneg
    (noncentralChiSixRadialSeriesKernel_nonneg a r hr.le)]
  unfold noncentralChiSixRadialSeriesKernel C
  have hseries := sixD_factorialSeries_le_exp_abs (a * r)
  have hr0 : 0 < r := hr
  have har : |a * r| = |a| * r := by
    rw [abs_mul, abs_of_pos hr0]
  rw [har] at hseries
  have hkernelExp : -((r ^ 2 + a ^ 2) / 2) + |a| * r =
      -((r - |a|) ^ 2 / 2) := by
    rw [← sq_abs a]
    ring
  have hgauss : -((r - |a|) ^ 2 / 2) ≤ a ^ 2 / 2 - (1 / 4 : ℝ) * r ^ 2 := by
    have hs : 0 ≤ (r - 2 * |a|) ^ 2 := sq_nonneg (r - 2 * |a|)
    rw [← sq_abs a]
    nlinarith
  have hpos : 0 ≤ Real.exp (-((r ^ 2 + a ^ 2) / 2)) := Real.exp_nonneg _
  have hfactor : 0 ≤ r ^ 5 / 4 := by positivity
  have hseries' :
      (∑' n : ℕ, ((a * r) ^ 2 / 4) ^ n /
        ((n.factorial : ℝ) * ((n + 2).factorial : ℝ))) ≤
        Real.exp (|a| * r) := by
    simpa [pow_two] using hseries
  have houter : 0 ≤ (r ^ 5 / 4) * Real.exp (-((r ^ 2 + a ^ 2) / 2)) :=
    mul_nonneg hfactor hpos
  calc
    (r ^ 5 / 4) * Real.exp (-((r ^ 2 + a ^ 2) / 2)) *
        (∑' n : ℕ, ((a * r) ^ 2 / 4) ^ n /
          ((n.factorial : ℝ) * ((n + 2).factorial : ℝ))) ≤
        (r ^ 5 / 4) * Real.exp (-((r ^ 2 + a ^ 2) / 2)) *
        Real.exp (|a| * r) := mul_le_mul_of_nonneg_left hseries' houter
    _ = (r ^ 5 / 4) *
        (Real.exp (-((r ^ 2 + a ^ 2) / 2)) * Real.exp (|a| * r)) := by ring
    _ = (r ^ 5 / 4) *
        Real.exp (-((r ^ 2 + a ^ 2) / 2) + |a| * r) := by
      rw [← Real.exp_add]
    _ = (r ^ 5 / 4) * Real.exp (-((r - |a|) ^ 2 / 2)) := by
      rw [hkernelExp]
    _ ≤ (r ^ 5 / 4) * Real.exp (a ^ 2 / 2 - (1 / 4 : ℝ) * r ^ 2) := by
      gcongr
    _ = C * (r ^ 5 * Real.exp (-(1 / 4 : ℝ) * r ^ 2)) := by
      dsimp [C]
      rw [show a ^ 2 / 2 - (1 / 4 : ℝ) * r ^ 2 =
        a ^ 2 / 2 + (-(1 / 4 : ℝ) * r ^ 2) by ring, Real.exp_add]
      ring

end

end JinWishart
