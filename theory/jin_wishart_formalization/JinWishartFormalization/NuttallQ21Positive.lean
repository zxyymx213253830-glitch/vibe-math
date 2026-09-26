import JinWishartFormalization.NoncentralFourDimensionalRadial
import JinWishartFormalization.BesselI0Angle
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Strict positivity and integrability of the `(p,q)=(2,1)` Nuttall-Q tail

This module develops the real order-one Bessel kernel needed for the first
nontrivial one-column case beyond a scalar complex sample.
-/

open MeasureTheory Set

namespace JinWishart

noncomputable section

private def besselI0RealSeries (y : ℝ) : ℝ :=
  ∑' n : ℕ, (y ^ 2 / 4) ^ n / ((n.factorial : ℝ) ^ 2)

private theorem summable_factorialProductSeries {z : ℝ} (hz : 0 ≤ z) :
    Summable fun n : ℕ => z ^ n /
      ((n.factorial : ℝ) * ((n + 1).factorial : ℝ)) := by
  apply (Real.summable_pow_div_factorial z).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  have hf : (1 : ℝ) ≤ (n.factorial : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.factorial_pos n))
  rw [Nat.factorial_succ]
  push_cast
  nlinarith [sq_nonneg ((n.factorial : ℝ) - 1)]

private theorem summable_factorialSquareSeries {z : ℝ} (hz : 0 ≤ z) :
    Summable fun n : ℕ => z ^ n / ((n.factorial : ℝ) ^ 2) := by
  apply (Real.summable_pow_div_factorial z).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  have hf : (1 : ℝ) ≤ (n.factorial : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.factorial_pos n))
  nlinarith [sq_nonneg ((n.factorial : ℝ) - 1)]

/-- For a strictly positive input, `I₁(y)` is strictly positive; the first
coefficient of the hypergeometric series supplies a positive lower bound. -/
theorem besselI1RealSeries_pos {y : ℝ} (hy : 0 < y) :
    0 < besselI1RealSeries y := by
  unfold besselI1RealSeries
  have hs := summable_factorialProductSeries (by positivity : 0 ≤ y ^ 2 / 4)
  have hseries :
      1 ≤ ∑' n : ℕ, (y ^ 2 / 4) ^ n /
        ((n.factorial : ℝ) * ((n + 1).factorial : ℝ)) := by
    have h := hs.le_tsum 0 (by
      intro n hn
      positivity)
    simpa using h
  exact mul_pos (div_pos hy (by norm_num)) (lt_of_lt_of_le zero_lt_one hseries)

private theorem besselI0RealSeries_le_exp {y : ℝ} (hy : 0 ≤ y) :
    besselI0RealSeries y ≤ Real.exp y := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have hangle :
      (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.exp (y * Real.cos θ)) ≤
        ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.exp y := by
    have hab : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    have hfcont : Continuous (fun θ : ℝ => Real.exp (y * Real.cos θ)) := by fun_prop
    have hf : IntervalIntegrable (fun θ : ℝ => Real.exp (y * Real.cos θ))
        volume 0 (2 * Real.pi) := hfcont.intervalIntegrable 0 (2 * Real.pi)
    have hgcont : Continuous (fun _ : ℝ => Real.exp y) := continuous_const
    have hg : IntervalIntegrable (fun _ : ℝ => Real.exp y)
        volume 0 (2 * Real.pi) := hgcont.intervalIntegrable 0 (2 * Real.pi)
    apply intervalIntegral.integral_mono_on (hab := hab) (hf := hf) (hg := hg)
    intro θ hθ
    apply Real.exp_le_exp.mpr
    simpa using mul_le_mul_of_nonneg_left (Real.cos_le_one θ) hy
  rw [angularExpIntegral_eq_factorialSeries] at hangle
  rw [intervalIntegral.integral_const, smul_eq_mul] at hangle
  simp only [sub_zero] at hangle
  unfold besselI0RealSeries
  exact (le_of_mul_le_mul_left hangle hpi).trans_eq (by ring)

/-- The order-one modified Bessel series satisfies `I₁(y) ≤ (y/2)eʸ` on
the nonnegative half-line. -/
theorem besselI1RealSeries_le_exp {y : ℝ} (hy : 0 ≤ y) :
    besselI1RealSeries y ≤ (y / 2) * Real.exp y := by
  have hz : 0 ≤ y ^ 2 / 4 := by positivity
  have hS1 := summable_factorialProductSeries hz
  have hS0 := summable_factorialSquareSeries hz
  have hcoeff : ∀ n : ℕ,
      (y ^ 2 / 4) ^ n /
          ((n.factorial : ℝ) * ((n + 1).factorial : ℝ)) ≤
        (y ^ 2 / 4) ^ n /
          ((n.factorial : ℝ) ^ 2) := by
    intro n
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have hf : (1 : ℝ) ≤ (n.factorial : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt (Nat.factorial_pos n))
    rw [Nat.factorial_succ]
    push_cast
    nlinarith [sq_nonneg ((n.factorial : ℝ) - 1)]
  have hseries := Summable.tsum_le_tsum hcoeff hS1 hS0
  have hI0 : besselI0RealSeries y ≤ Real.exp y := besselI0RealSeries_le_exp hy
  unfold besselI1RealSeries
  exact mul_le_mul_of_nonneg_left (hseries.trans hI0) (div_nonneg hy (by norm_num))

/-- The real `(2,1)` Nuttall-Q integrand. -/
def nuttallQ21RealKernel (a t : ℝ) : ℝ :=
  t ^ 2 * Real.exp (-((t ^ 2 + a ^ 2) / 2)) * besselI1RealSeries (a * t)

/-- The real kernel agrees with the real part of the complex kernel from
`NuttallQ.lean`. -/
theorem nuttallQ21RealKernel_eq_complexRealPart (a t : ℝ) :
    nuttallQ21RealKernel a t =
      t ^ 2 * Real.exp (-((t ^ 2 + a ^ 2) / 2)) *
        (modifiedBesselI 1 ((a * t : ℝ) : ℂ)).re := by
  have hI := modifiedBesselI_one_ofReal_eq_realSeries (a * t)
  have hIre := congrArg Complex.re hI
  have hseries : besselI1RealSeries (a * t) =
      (modifiedBesselI 1 ((a * t : ℝ) : ℂ)).re := by
    simpa [besselI1RealSeries] using hIre
  simp only [nuttallQ21RealKernel]
  rw [hseries]

/-- The complex Nuttall-Q `(2,1)` integrand is the complex embedding of the
real kernel. -/
theorem nuttallQ21Integrand_eq_realKernel (a t : ℝ) :
    nuttallQIntegrand 2 1 a t = (nuttallQ21RealKernel a t : ℂ) := by
  simp only [nuttallQIntegrand, nuttallQ21RealKernel, besselI1RealSeries]
  rw [← modifiedBesselI_one_ofReal_eq_realSeries]
  push_cast
  rfl

/-- The real `(2,1)` kernel is positive for positive amplitude and radius. -/
theorem nuttallQ21RealKernel_pos {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    0 < nuttallQ21RealKernel a t := by
  unfold nuttallQ21RealKernel
  exact mul_pos (mul_pos (sq_pos_of_pos ht) (Real.exp_pos _))
    (besselI1RealSeries_pos (mul_pos ha ht))

/-- A Gaussian tail majorant for the real `(2,1)` kernel. -/
theorem nuttallQ21RealKernel_le_gaussianMajorant {a t : ℝ}
    (ha : 0 ≤ a) (ht : 0 ≤ t) :
    nuttallQ21RealKernel a t ≤
      (a / 2) * Real.exp (a ^ 2 / 2) *
        (t ^ 3 * Real.exp (-(1 / 4 : ℝ) * t ^ 2)) := by
  have hat : 0 ≤ a * t := mul_nonneg ha ht
  have hI := besselI1RealSeries_le_exp hat
  have hsq : 0 ≤ (t - 2 * a) ^ 2 := sq_nonneg (t - 2 * a)
  have hexp : -((t - a) ^ 2 / 2) ≤ a ^ 2 / 2 - (1 / 4 : ℝ) * t ^ 2 := by
    nlinarith
  have hkernelExp : -((t ^ 2 + a ^ 2) / 2) + a * t =
      -((t - a) ^ 2 / 2) := by ring
  unfold nuttallQ21RealKernel
  calc
    _ ≤ t ^ 2 * Real.exp (-((t ^ 2 + a ^ 2) / 2)) *
        ((a * t / 2) * Real.exp (a * t)) :=
      mul_le_mul_of_nonneg_left hI (by positivity)
    _ = (a / 2) * t ^ 3 *
        Real.exp (-((t ^ 2 + a ^ 2) / 2) + a * t) := by
      rw [Real.exp_add]
      ring_nf
    _ = (a / 2) * t ^ 3 * Real.exp (-((t - a) ^ 2 / 2)) := by rw [hkernelExp]
    _ ≤ (a / 2) * t ^ 3 *
        Real.exp (a ^ 2 / 2 - (1 / 4 : ℝ) * t ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      · exact Real.exp_le_exp.mpr hexp
      · positivity
    _ = (a / 2) * Real.exp (a ^ 2 / 2) *
        (t ^ 3 * Real.exp (-(1 / 4 : ℝ) * t ^ 2)) := by
      calc
        _ = (a / 2) * t ^ 3 *
            (Real.exp (a ^ 2 / 2) * Real.exp (-(1 / 4 : ℝ) * t ^ 2)) := by
          rw [← Real.exp_add]
          ring_nf
        _ = _ := by ring_nf

theorem nuttallQ21RealKernel_nonneg_of_nonneg {a t : ℝ}
    (ha : 0 ≤ a) (ht : 0 ≤ t) : 0 ≤ nuttallQ21RealKernel a t := by
  unfold nuttallQ21RealKernel
  exact mul_nonneg (mul_nonneg (sq_nonneg t) (Real.exp_pos _).le)
    (besselI1RealSeries_nonneg (mul_nonneg ha ht))

/-- The real `(2,1)` Nuttall-Q kernel is integrable on the positive
half-line. -/
theorem nuttallQ21RealKernel_integrableOn_Ioi (a : ℝ) (ha : 0 ≤ a) :
    IntegrableOn (nuttallQ21RealKernel a) (Ioi 0) := by
  have hbase : IntegrableOn
      (fun t : ℝ => t ^ 3 * Real.exp (-(1 / 4 : ℝ) * t ^ 2)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_sq
      (b := (1 / 4 : ℝ)) (s := (3 : ℝ)) (by norm_num) (by norm_num)
    apply (integrableOn_congr_fun (s := Ioi (0 : ℝ)) ?_ measurableSet_Ioi).2 h
    intro t ht
    change t ^ 3 * Real.exp (-(1 / 4 : ℝ) * t ^ 2) =
      Real.rpow t (3 : ℝ) * Real.exp (-(1 / 4 : ℝ) * t ^ 2)
    simp
  have hmajor : IntegrableOn
      (fun t : ℝ => (a / 2) * Real.exp (a ^ 2 / 2) *
        (t ^ 3 * Real.exp (-(1 / 4 : ℝ) * t ^ 2))) (Ioi 0) := by
    exact hbase.const_mul ((a / 2) * Real.exp (a ^ 2 / 2))
  have hcont : Continuous (fun t : ℝ =>
      t ^ 2 * Real.exp (-((t ^ 2 + a ^ 2) / 2)) *
        (modifiedBesselI 1 ((a * t : ℝ) : ℂ)).re) := by
    have hB : Continuous (fun t : ℝ =>
        (modifiedBesselI 1 ((a * t : ℝ) : ℂ)).re) :=
      Complex.continuous_re.comp ((continuous_modifiedBesselI 1).comp (by fun_prop))
    exact (continuous_id.pow 2).mul
      (Real.continuous_exp.comp (by fun_prop)) |>.mul hB
  have hcontKernel : Continuous (nuttallQ21RealKernel a) := by
    apply hcont.congr
    intro t
    exact (nuttallQ21RealKernel_eq_complexRealPart a t).symm
  have hmeas : AEStronglyMeasurable (nuttallQ21RealKernel a)
      (volume.restrict (Ioi 0)) :=
    hcontKernel.measurable.aestronglyMeasurable
  apply Integrable.mono' hmajor hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg
    (nuttallQ21RealKernel_nonneg_of_nonneg ha (le_of_lt ht))]
  exact nuttallQ21RealKernel_le_gaussianMajorant ha (le_of_lt ht)

/-- The real `(2,1)` Nuttall-Q tail is strictly positive at zero threshold
for every positive noncentrality amplitude. -/
theorem nuttallQ21RealIntegral_pos (a : ℝ) (ha : 0 < a) :
    0 < ∫ t in Ioi (0 : ℝ), nuttallQ21RealKernel a t := by
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      nuttallQ21RealKernel a := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (nuttallQ21RealKernel_nonneg_of_nonneg ha.le ht.le)
  have hint := nuttallQ21RealKernel_integrableOn_Ioi a ha.le
  have hsupport : Function.support (nuttallQ21RealKernel a) ∩ Ioi (0 : ℝ) =
      Ioi (0 : ℝ) := by
    ext t
    constructor
    · intro ht
      exact ht.2
    · intro ht
      constructor
      · rw [Function.mem_support]
        exact (nuttallQ21RealKernel_pos ha ht).ne'
      · exact ht
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnonneg hint]
  rw [hsupport, Real.volume_Ioi]
  exact ENNReal.zero_lt_top

/-- The complex Nuttall-Q tail `Q_{2,1}(a,0)` is nonzero for positive `a`.
The proof is by identifying its defining complex integral with the positive
real-kernel integral. -/
theorem nuttallQ21_zeroThreshold_ne_zero (a : ℝ) (ha : 0 < a) :
    nuttallQ 2 1 a 0 ≠ 0 := by
  have hreal := nuttallQ21RealIntegral_pos a ha
  have hident : nuttallQ 2 1 a 0 =
      (∫ t in Ioi (0 : ℝ), nuttallQ21RealKernel a t : ℝ) := by
    unfold nuttallQ
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact nuttallQ21Integrand_eq_realKernel a t
  rw [hident]
  exact Complex.ofReal_ne_zero.mpr hreal.ne'

end

end JinWishart
