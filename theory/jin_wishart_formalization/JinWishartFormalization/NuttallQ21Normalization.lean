import JinWishartFormalization.NuttallQ21Positive
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Normalization of the `(2,1)` Nuttall-Q tail

The intended proof expands the order-one Bessel series, evaluates the resulting
Gaussian moments, and sums the exponential series.  It uses only one-dimensional
real integration and does not assume a spherical-coordinate formula.
-/

open MeasureTheory Set

namespace JinWishart

noncomputable section

/-- Odd Gaussian moments in the normalization used by the Nuttall kernel. -/
theorem gaussianOddMoment (n : ℕ) :
    ∫ t in Ioi (0 : ℝ), t ^ (2 * n + 3) * Real.exp (-(t ^ 2 / 2)) =
      2 ^ (n + 1) * ((n + 1).factorial : ℝ) := by
  let g : ℝ → ℝ := fun y => (1 / 2 : ℝ) * y ^ (n + 1) * Real.exp (-(y / 2))
  have hchange := integral_comp_rpow_Ioi_of_pos (g := g) (p := (2 : ℝ)) (by norm_num)
  have hleft : (∫ t in Ioi (0 : ℝ), (2 * t) • g (t ^ 2)) =
      ∫ t in Ioi (0 : ℝ), t ^ (2 * n + 3) * Real.exp (-(t ^ 2 / 2)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    simp only [g, smul_eq_mul]
    ring
  have hchange' : (∫ t in Ioi (0 : ℝ), (2 * t) • g (t ^ 2)) =
      ∫ y in Ioi (0 : ℝ), g y := by
    calc
      _ = ∫ t in Ioi (0 : ℝ), (2 * t) • g (t ^ (2 : ℝ)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        change (2 * t) * g (t ^ (2 : ℕ)) = (2 * t) * g (t ^ (2 : ℝ))
        exact congrArg (fun z : ℝ => (2 * t) * g z)
          (Real.rpow_natCast t 2).symm
      _ = _ := by
        simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one] using hchange
  rw [hleft] at hchange'
  rw [hchange']
  rw [show (∫ y in Ioi (0 : ℝ), g y) =
      (1 / 2 : ℝ) * ∫ y in Ioi (0 : ℝ), y ^ (n + 1) * Real.exp (-(y / 2)) by
        calc
          _ = ∫ y in Ioi (0 : ℝ), (1 / 2 : ℝ) *
              (y ^ (n + 1) * Real.exp (-(y / 2))) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro y hy
            simp [g, mul_assoc]
          _ = _ := by rw [integral_const_mul]]
  have hgamma := Real.integral_rpow_mul_exp_neg_mul_Ioi
      (a := (n : ℝ) + 2) (r := (1 / 2 : ℝ)) (by positivity) (by norm_num)
  have hmoment : ∫ y in Ioi (0 : ℝ), y ^ (n + 1) * Real.exp (-(y / 2)) =
      2 ^ (n + 2) * ((n + 1).factorial : ℝ) := by
    calc
      _ = ∫ y in Ioi (0 : ℝ), y ^ ((n : ℝ) + 2 - 1) *
          Real.exp (-(1 / 2 * y)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro y hy
        change y ^ (n + 1) * Real.exp (-(y / 2)) =
          y ^ ((n : ℝ) + 2 - 1) * Real.exp (-(1 / 2 * y))
        have hexp : -(y / 2) = -(1 / 2 * y) := by ring
        have hpow : (n : ℝ) + 2 - 1 = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
        rw [hexp, hpow, Real.rpow_natCast]
      _ = (1 / (1 / 2 : ℝ)) ^ ((n : ℝ) + 2) * Real.Gamma ((n : ℝ) + 2) := hgamma
      _ = 2 ^ (n + 2) * ((n + 1).factorial : ℝ) := by
        have hcast : (n : ℝ) + 2 = ((n + 2 : ℕ) : ℝ) := by push_cast; ring
        have harg : ((n + 2 : ℕ) : ℝ) = ((n + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
        rw [hcast, harg, Real.Gamma_nat_eq_factorial]
        rw [show (1 / (1 / 2 : ℝ) : ℝ) = 2 by norm_num, ← harg,
          Real.rpow_natCast]
  rw [hmoment]
  ring

/-- The `n`th nonnegative summand of the expanded `(2,1)` radial kernel. -/
def nuttallQ21SeriesTerm (a : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  t ^ 2 * Real.exp (-((t ^ 2 + a ^ 2) / 2)) * (a * t / 2) *
    (((a * t) ^ 2 / 4) ^ n /
      ((n.factorial : ℝ) * ((n + 1).factorial : ℝ)))

/-- The real Nuttall kernel is the pointwise sum of its positive Bessel-series
terms. -/
theorem nuttallQ21RealKernel_eq_tsum (a t : ℝ) :
    nuttallQ21RealKernel a t = ∑' n : ℕ, nuttallQ21SeriesTerm a n t := by
  unfold nuttallQ21RealKernel besselI1RealSeries nuttallQ21SeriesTerm
  calc
    _ = t ^ 2 * Real.exp (-((t ^ 2 + a ^ 2) / 2)) *
        ((a * t / 2) * ∑' n : ℕ,
          ((a * t) ^ 2 / 4) ^ n /
            ((n.factorial : ℝ) * ((n + 1).factorial : ℝ))) := by ring
    _ = (t ^ 2 * Real.exp (-((t ^ 2 + a ^ 2) / 2)) * (a * t / 2)) *
        ∑' n : ℕ, ((a * t) ^ 2 / 4) ^ n /
          ((n.factorial : ℝ) * ((n + 1).factorial : ℝ)) := by ring
    _ = ∑' n : ℕ, (t ^ 2 * Real.exp (-((t ^ 2 + a ^ 2) / 2)) *
        (a * t / 2)) * (((a * t) ^ 2 / 4) ^ n /
          ((n.factorial : ℝ) * ((n + 1).factorial : ℝ))) := by
      rw [← tsum_mul_left]

/-- Integrating one Bessel-series term reduces to the corresponding odd
Gaussian moment. -/
theorem nuttallQ21SeriesTerm_integral (a : ℝ) (n : ℕ) :
    ∫ t in Ioi (0 : ℝ), nuttallQ21SeriesTerm a n t =
      (Real.exp (-(a ^ 2 / 2)) * (a / 2) *
        ((a ^ 2 / 4) ^ n /
          ((n.factorial : ℝ) * ((n + 1).factorial : ℝ)))) *
        (2 ^ (n + 1) * ((n + 1).factorial : ℝ)) := by
  have hfactor (t : ℝ) :
      nuttallQ21SeriesTerm a n t =
        (Real.exp (-(a ^ 2 / 2)) * (a / 2) *
          ((a ^ 2 / 4) ^ n /
            ((n.factorial : ℝ) * ((n + 1).factorial : ℝ)))) *
          (t ^ (2 * n + 3) * Real.exp (-(t ^ 2 / 2))) := by
    unfold nuttallQ21SeriesTerm
    have hpow : ((a * t) ^ 2 / 4) ^ n =
        (a ^ 2 / 4) ^ n * (t ^ 2) ^ n := by
      rw [show (a * t) ^ 2 / 4 = (a ^ 2 / 4) * t ^ 2 by ring, mul_pow]
    rw [hpow]
    have htpow : t ^ 2 * (t ^ 2) ^ n * t = t ^ (2 * n + 3) := by
      calc
        t ^ 2 * (t ^ 2) ^ n * t = t ^ 2 * t ^ (2 * n) * t := by rw [← pow_mul]
        _ = t ^ (2 + 2 * n) * t := by rw [← pow_add]
        _ = t ^ (2 + 2 * n + 1) := by rw [← pow_succ]
        _ = t ^ (2 * n + 3) := by congr 1 <;> omega
    have hexp : -((t ^ 2 + a ^ 2) / 2) = -(a ^ 2 / 2) - t ^ 2 / 2 := by ring
    calc
      _ = (Real.exp (-(a ^ 2 / 2)) * (a / 2) *
          ((a ^ 2 / 4) ^ n /
            ((n.factorial : ℝ) * ((n + 1).factorial : ℝ)))) *
          (t ^ 2 * (t ^ 2) ^ n * t * Real.exp (-(t ^ 2 / 2))) := by
        rw [hexp, sub_eq_add_neg, Real.exp_add]
        ring
      _ = _ := by rw [htpow]
  rw [show (fun t : ℝ => nuttallQ21SeriesTerm a n t) =
      fun t => (Real.exp (-(a ^ 2 / 2)) * (a / 2) *
        ((a ^ 2 / 4) ^ n /
          ((n.factorial : ℝ) * ((n + 1).factorial : ℝ)))) *
        (t ^ (2 * n + 3) * Real.exp (-(t ^ 2 / 2))) by
          funext t
          exact hfactor t]
  rw [integral_const_mul, gaussianOddMoment]

/-- Closed form for the integral of one expanded Nuttall summand. -/
theorem nuttallQ21SeriesTerm_integral_closed (a : ℝ) (n : ℕ) :
    ∫ t in Ioi (0 : ℝ), nuttallQ21SeriesTerm a n t =
      a * Real.exp (-(a ^ 2 / 2)) *
        ((a ^ 2 / 2) ^ n / (n.factorial : ℝ)) := by
  rw [nuttallQ21SeriesTerm_integral]
  have hfact : (n.factorial : ℝ) ≠ 0 := by positivity
  have hfact' : ((n + 1).factorial : ℝ) ≠ 0 := by positivity
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, div_pow]
  field_simp [hfact, hfact']
  rw [pow_succ]
  rw [show a ^ 1 * a = a ^ 2 by rw [pow_one, pow_two]]
  have hpow : (2 : ℝ) ^ n * (a ^ 2) ^ n = (2 * a ^ 2) ^ n := by
    rw [← mul_pow]
  have hpow' : (2 ^ 2 : ℝ) ^ n * (a ^ 2 / 2) ^ n = (2 * a ^ 2) ^ n := by
    rw [← mul_pow]
    congr 1
    ring
  calc
    _ = a * 2 * (2 ^ n * (a ^ 2) ^ n) := by rw [pow_succ]; ring
    _ = a * 2 * (2 * a ^ 2) ^ n := by rw [hpow]
    _ = a * 2 * ((2 ^ 2 : ℝ) ^ n * (a ^ 2 / 2) ^ n) := by rw [hpow']
    _ = _ := by ring

/-- The zero-threshold real Nuttall integral is exactly the noncentrality
amplitude. -/
theorem nuttallQ21RealIntegral_eq_amplitude (a : ℝ) (ha : 0 < a) :
    ∫ t in Ioi (0 : ℝ), nuttallQ21RealKernel a t = a := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  have hFint : ∀ n : ℕ, Integrable (fun t : ℝ => nuttallQ21SeriesTerm a n t) μ := by
    intro n
    have hpos : 0 < ∫ t in Ioi (0 : ℝ), nuttallQ21SeriesTerm a n t := by
      rw [nuttallQ21SeriesTerm_integral_closed]
      have hbase : 0 < a ^ 2 / 2 := by positivity
      exact mul_pos (mul_pos ha (Real.exp_pos _))
        (div_pos (pow_pos hbase _) (by positivity))
    exact .of_integral_ne_zero (by simpa [μ] using hpos.ne')
  have hnorm (n : ℕ) :
      (∫ t, ‖nuttallQ21SeriesTerm a n t‖ ∂μ) =
        a * Real.exp (-(a ^ 2 / 2)) *
          ((a ^ 2 / 2) ^ n / (n.factorial : ℝ)) := by
    calc
      _ = ∫ t, nuttallQ21SeriesTerm a n t ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have hterm : 0 ≤ nuttallQ21SeriesTerm a n t := by
          have ht0 : 0 < t := ht
          unfold nuttallQ21SeriesTerm
          positivity
        rw [Real.norm_eq_abs, abs_of_nonneg hterm]
      _ = _ := by
        simpa [μ] using nuttallQ21SeriesTerm_integral_closed a n
  have hsum_norm : Summable fun n : ℕ => ∫ t, ‖nuttallQ21SeriesTerm a n t‖ ∂μ := by
    have hs := (Real.summable_pow_div_factorial (a ^ 2 / 2)).mul_left
      (a * Real.exp (-(a ^ 2 / 2)))
    refine hs.congr ?_
    intro n
    exact (hnorm n).symm
  have hsum_integral :
      ∑' n : ℕ, (∫ t, nuttallQ21SeriesTerm a n t ∂μ) = a := by
    calc
      _ = ∑' n : ℕ, a * Real.exp (-(a ^ 2 / 2)) *
          ((a ^ 2 / 2) ^ n / (n.factorial : ℝ)) := by
        apply tsum_congr
        intro n
        rw [nuttallQ21SeriesTerm_integral_closed]
      _ = (a * Real.exp (-(a ^ 2 / 2))) *
          ∑' n : ℕ, (a ^ 2 / 2) ^ n / (n.factorial : ℝ) := by
        rw [tsum_mul_left]
      _ = a := by
        have hexp (x : ℝ) : ∑' n : ℕ, x ^ n / (n.factorial : ℝ) = Real.exp x := by
          rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
          apply tsum_congr
          intro n
          simp [div_eq_mul_inv, smul_eq_mul, mul_comm]
        rw [hexp (a ^ 2 / 2)]
        calc
          _ = a * (Real.exp (-(a ^ 2 / 2)) * Real.exp (a ^ 2 / 2)) := by ring
          _ = a * Real.exp (-(a ^ 2 / 2) + a ^ 2 / 2) := by rw [← Real.exp_add]
          _ = a := by rw [neg_add_cancel, Real.exp_zero, mul_one]
  calc
    _ = ∫ t, (∑' n : ℕ, nuttallQ21SeriesTerm a n t) ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact nuttallQ21RealKernel_eq_tsum a t
    _ = ∑' n : ℕ, (∫ t, nuttallQ21SeriesTerm a n t ∂μ) :=
      (integral_tsum_of_summable_integral_norm hFint hsum_norm).symm
    _ = a := hsum_integral

/-- The complex Nuttall-Q normalization at zero threshold follows from the
real integral normalization. -/
theorem nuttallQ21_zeroThreshold_eq_amplitude (a : ℝ) (ha : 0 < a) :
    nuttallQ 2 1 a 0 = (a : ℂ) := by
  have hident : nuttallQ 2 1 a 0 =
      (∫ t in Ioi (0 : ℝ), nuttallQ21RealKernel a t : ℝ) := by
    unfold nuttallQ
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact nuttallQ21Integrand_eq_realKernel a t
  rw [hident]
  exact congrArg Complex.ofReal (nuttallQ21RealIntegral_eq_amplitude a ha)

end

end JinWishart
