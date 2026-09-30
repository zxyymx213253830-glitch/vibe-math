import JinWishartFormalization.SixDimensionalAngularBesselI2

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Sets.Compacts

/-!
# Eight-dimensional axial angular integral (analytic part)

This file isolates the one-angle `sin⁶` integral required by the axial
noncentral Gaussian calculation in real dimension eight.  It proves the
factorial-series identity directly.  It does not identify this angle chart
with the geometric pushforward of surface measure on `S⁷`; that is a separate
measure-geometry theorem.
-/

namespace JinWishart

open MeasureTheory Set

/-- The order-three modified-Bessel factorial series, in a denominator-free
normalization suitable at `a = 0`. -/
noncomputable def besselI3RealSeries (a : ℝ) : ℝ :=
  (a ^ 3 / 8) * ∑' n : ℕ,
    (a ^ 2 / 4) ^ n / ((n.factorial : ℝ) * ((n + 3).factorial : ℝ))

/-- Taylor summand for the `sin⁶` axial exponential integral. -/
noncomputable def expCosSinSixTerm (a : ℝ) (n : ℕ) : ContinuousMap ℝ ℝ :=
  ⟨fun θ => Real.sin θ ^ 6 * (a * Real.cos θ) ^ n / (n.factorial : ℝ), by fun_prop⟩

theorem expCosSinSixTerm_tsum (a θ : ℝ) :
    ∑' n : ℕ, expCosSinSixTerm a n θ =
      Real.sin θ ^ 6 * Real.exp (a * Real.cos θ) := by
  calc
    ∑' n : ℕ, expCosSinSixTerm a n θ =
        ∑' n : ℕ, Real.sin θ ^ 6 * expCosPowerTerm a n θ := by
      apply tsum_congr
      intro n
      change Real.sin θ ^ 6 * (a * Real.cos θ) ^ n / (n.factorial : ℝ) =
        Real.sin θ ^ 6 * ((a * Real.cos θ) ^ n / (n.factorial : ℝ))
      ring
    _ = Real.sin θ ^ 6 * ∑' n : ℕ, expCosPowerTerm a n θ := tsum_mul_left
    _ = _ := by rw [expCosPowerTerm_tsum]

theorem expCosSinSixTerm_restrict_norm_le (a : ℝ) (n : ℕ) :
    ‖(expCosSinSixTerm a n).restrict
      (⟨uIcc (0 : ℝ) Real.pi, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖ ≤
      |a| ^ n / (n.factorial : ℝ) := by
  rw [ContinuousMap.norm_le (f := (expCosSinSixTerm a n).restrict
    (⟨uIcc (0 : ℝ) Real.pi, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ))
    (by positivity : 0 ≤ |a| ^ n / (n.factorial : ℝ))]
  intro θ
  change |Real.sin (θ : ℝ) ^ 6 * (a * Real.cos (θ : ℝ)) ^ n /
    (n.factorial : ℝ)| ≤ _
  have hs : |Real.sin (θ : ℝ)| ≤ 1 := Real.abs_sin_le_one _
  have hc : |Real.cos (θ : ℝ)| ≤ 1 := Real.abs_cos_le_one _
  have hf : 0 < (n.factorial : ℝ) := by positivity
  rw [abs_div, abs_mul, abs_pow, abs_of_pos hf, abs_pow, abs_mul]
  calc
    |Real.sin (θ : ℝ)| ^ 6 * (|a| * |Real.cos (θ : ℝ)|) ^ n /
        (n.factorial : ℝ) ≤ 1 ^ 6 * (|a| * 1) ^ n / (n.factorial : ℝ) := by
          gcongr
    _ = |a| ^ n / (n.factorial : ℝ) := by simp

theorem summable_expCosSinSixTerm_restrict_norm (a : ℝ) :
    Summable fun n : ℕ => ‖(expCosSinSixTerm a n).restrict
      (⟨uIcc (0 : ℝ) Real.pi, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖ := by
  apply (Real.summable_pow_div_factorial |a|).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact expCosSinSixTerm_restrict_norm_le a n

theorem angularSinSixIntegral_eq_tsum (a : ℝ) :
    (∫ θ in (0 : ℝ)..Real.pi, Real.sin θ ^ 6 * Real.exp (a * Real.cos θ)) =
      ∑' n : ℕ, ∫ θ in (0 : ℝ)..Real.pi,
        Real.sin θ ^ 6 * (a * Real.cos θ) ^ n / (n.factorial : ℝ) := by
  calc
    _ = ∫ θ in (0 : ℝ)..Real.pi,
        ∑' n : ℕ, expCosSinSixTerm a n θ := by
      apply intervalIntegral.integral_congr
      intro θ _
      exact (expCosSinSixTerm_tsum a θ).symm
    _ = ∑' n : ℕ, ∫ θ in (0 : ℝ)..Real.pi, expCosSinSixTerm a n θ := by
      symm
      exact intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm
        (summable_expCosSinSixTerm_restrict_norm a)
    _ = _ := by
      apply tsum_congr
      intro n
      rfl

private theorem expSinSixTerm_integral_norm_le (a : ℝ) (n : ℕ) :
    ‖∫ θ in (0 : ℝ)..Real.pi,
      Real.sin θ ^ 6 * (a * Real.cos θ) ^ n / (n.factorial : ℝ)‖ ≤
        Real.pi * (|a| ^ n / (n.factorial : ℝ)) := by
  let C : ℝ := |a| ^ n / (n.factorial : ℝ)
  have hpoint : ∀ θ ∈ uIoc (0 : ℝ) Real.pi,
      ‖Real.sin θ ^ 6 * (a * Real.cos θ) ^ n /
        (n.factorial : ℝ)‖ ≤ C := by
    intro θ hθ
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow,
      abs_of_pos (by positivity : 0 < (n.factorial : ℝ)), abs_pow, abs_mul]
    dsimp [C]
    have hs : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one _
    have hc : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one _
    calc
      |Real.sin θ| ^ 6 * (|a| * |Real.cos θ|) ^ n /
          (n.factorial : ℝ) ≤ 1 ^ 6 * (|a| * 1) ^ n /
            (n.factorial : ℝ) := by gcongr
      _ = |a| ^ n / (n.factorial : ℝ) := by simp
  calc
    _ ≤ (|a| ^ n / (n.factorial : ℝ)) * |Real.pi - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ = Real.pi * (|a| ^ n / (n.factorial : ℝ)) := by
      rw [sub_zero, abs_of_pos Real.pi_pos]
      ring

private theorem summable_expSinSixTerm_integrals (a : ℝ) :
    Summable fun n : ℕ => ∫ θ in (0 : ℝ)..Real.pi,
      Real.sin θ ^ 6 * (a * Real.cos θ) ^ n / (n.factorial : ℝ) := by
  apply (Real.summable_pow_div_factorial |a|).mul_left Real.pi |>.of_norm_bounded
  intro n
  simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
    expSinSixTerm_integral_norm_le a n

private theorem sinSix_even_cos_moment (k : ℕ) :
    (∫ θ in (0 : ℝ)..Real.pi,
      Real.sin θ ^ 6 * Real.cos θ ^ (2 * k)) =
      (15 * Real.pi / 8) *
        ((Nat.factorial (2 * k) : ℝ) /
          (4 ^ k * (Nat.factorial k : ℝ) * (Nat.factorial (k + 3) : ℝ))) := by
  have hsin : ∀ θ : ℝ, Real.sin θ ^ 6 * Real.cos θ ^ (2 * k) =
      Real.cos θ ^ (2 * k) - 3 * Real.cos θ ^ (2 * k + 2) +
        3 * Real.cos θ ^ (2 * k + 4) - Real.cos θ ^ (2 * k + 6) := by
    intro θ
    have hs : Real.sin θ ^ 6 = (1 - Real.cos θ ^ 2) ^ 3 := by
      calc
        Real.sin θ ^ 6 = (Real.sin θ ^ 2) ^ 3 := by ring
        _ = (1 - Real.cos θ ^ 2) ^ 3 := by rw [Real.sin_sq]
    rw [hs]
    ring
  have hInt (j : ℕ) : IntervalIntegrable (fun θ : ℝ => Real.cos θ ^ j)
      volume 0 Real.pi := (Real.continuous_cos.pow j).intervalIntegrable _ _
  rw [show (fun θ : ℝ => Real.sin θ ^ 6 * Real.cos θ ^ (2 * k)) =
      fun θ => Real.cos θ ^ (2 * k) - 3 * Real.cos θ ^ (2 * k + 2) +
        3 * Real.cos θ ^ (2 * k + 4) - Real.cos θ ^ (2 * k + 6) by
          funext θ; exact hsin θ]
  have h2 : IntervalIntegrable
      (fun θ : ℝ => (3 : ℝ) * Real.cos θ ^ (2 * k + 2)) volume 0 Real.pi :=
    (hInt _).const_mul 3
  have h4 : IntervalIntegrable
      (fun θ : ℝ => (3 : ℝ) * Real.cos θ ^ (2 * k + 4)) volume 0 Real.pi :=
    (hInt _).const_mul 3
  have hleft : IntervalIntegrable
      (fun θ : ℝ => Real.cos θ ^ (2 * k) -
        3 * Real.cos θ ^ (2 * k + 2) +
        3 * Real.cos θ ^ (2 * k + 4)) volume 0 Real.pi :=
    ((hInt _).sub h2).add h4
  rw [intervalIntegral.integral_sub hleft (hInt _)]
  rw [intervalIntegral.integral_add ((hInt _).sub h2) h4,
    intervalIntegral.integral_sub (hInt _) h2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [show 2 * k + 2 = 2 * (k + 1) by omega,
    show 2 * k + 4 = 2 * (k + 2) by omega,
    show 2 * k + 6 = 2 * (k + 3) by omega,
    integral_cos_pow_zero_pi_even, integral_cos_pow_zero_pi_even,
    integral_cos_pow_zero_pi_even, integral_cos_pow_zero_pi_even]
  push_cast
  rw [show 2 * (k + 1) = 2 * k + 2 by omega,
    show 2 * (k + 2) = 2 * k + 4 by omega,
    show 2 * (k + 3) = 2 * k + 6 by omega]
  have hf0 : (Nat.factorial k : ℝ) ≠ 0 := by positivity
  have hf3 : (Nat.factorial (k + 3) : ℝ) ≠ 0 := by positivity
  have hp : (4 : ℝ) ^ k ≠ 0 := by positivity
  rw [Nat.factorial_succ (2 * k + 5), Nat.factorial_succ (2 * k + 4),
    Nat.factorial_succ (2 * k + 3), Nat.factorial_succ (2 * k + 2),
    Nat.factorial_succ (2 * k + 1), Nat.factorial_succ (2 * k),
    Nat.factorial_succ (k + 2), Nat.factorial_succ (k + 1),
    Nat.factorial_succ k]
  simp only [pow_succ]
  push_cast
  field_simp [hf0, hf3, hp]
  <;> ring_nf

private theorem sinSix_odd_cos_moment (k : ℕ) :
    (∫ θ in (0 : ℝ)..Real.pi,
      Real.sin θ ^ 6 * Real.cos θ ^ (2 * k + 1)) = 0 := by
  have hsin : ∀ θ : ℝ, Real.sin θ ^ 6 * Real.cos θ ^ (2 * k + 1) =
      Real.cos θ ^ (2 * k + 1) - 3 * Real.cos θ ^ (2 * k + 3) +
        3 * Real.cos θ ^ (2 * k + 5) - Real.cos θ ^ (2 * k + 7) := by
    intro θ
    have hs : Real.sin θ ^ 6 = (1 - Real.cos θ ^ 2) ^ 3 := by
      calc
        Real.sin θ ^ 6 = (Real.sin θ ^ 2) ^ 3 := by ring
        _ = (1 - Real.cos θ ^ 2) ^ 3 := by rw [Real.sin_sq]
    rw [hs]
    ring
  rw [show (fun θ : ℝ => Real.sin θ ^ 6 * Real.cos θ ^ (2 * k + 1)) =
      fun θ => Real.cos θ ^ (2 * k + 1) - 3 * Real.cos θ ^ (2 * k + 3) +
        3 * Real.cos θ ^ (2 * k + 5) - Real.cos θ ^ (2 * k + 7) by
          funext θ; exact hsin θ]
  have h1 : IntervalIntegrable (fun θ : ℝ => Real.cos θ ^ (2 * k + 1))
      volume 0 Real.pi := (Real.continuous_cos.pow _).intervalIntegrable _ _
  have h3 : IntervalIntegrable (fun θ : ℝ => Real.cos θ ^ (2 * k + 3))
      volume 0 Real.pi := (Real.continuous_cos.pow _).intervalIntegrable _ _
  have h5 : IntervalIntegrable (fun θ : ℝ => Real.cos θ ^ (2 * k + 5))
      volume 0 Real.pi := (Real.continuous_cos.pow _).intervalIntegrable _ _
  have h7 : IntervalIntegrable (fun θ : ℝ => Real.cos θ ^ (2 * k + 7))
      volume 0 Real.pi := (Real.continuous_cos.pow _).intervalIntegrable _ _
  have h3s : IntervalIntegrable
      (fun θ : ℝ => (3 : ℝ) * Real.cos θ ^ (2 * k + 3)) volume 0 Real.pi :=
    h3.const_mul 3
  have h5s : IntervalIntegrable
      (fun θ : ℝ => (3 : ℝ) * Real.cos θ ^ (2 * k + 5)) volume 0 Real.pi :=
    h5.const_mul 3
  have hleft : IntervalIntegrable
      (fun θ : ℝ => Real.cos θ ^ (2 * k + 1) -
        3 * Real.cos θ ^ (2 * k + 3) +
        3 * Real.cos θ ^ (2 * k + 5)) volume 0 Real.pi :=
    (h1.sub h3s).add h5s
  rw [intervalIntegral.integral_sub hleft h7]
  rw [intervalIntegral.integral_add (h1.sub h3s) h5s,
    intervalIntegral.integral_sub h1 h3s,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [show 2 * k + 3 = 2 * (k + 1) + 1 by omega,
      show 2 * k + 5 = 2 * (k + 2) + 1 by omega,
      show 2 * k + 7 = 2 * (k + 3) + 1 by omega,
      integral_cos_pow_zero_pi_odd, integral_cos_pow_zero_pi_odd,
      integral_cos_pow_zero_pi_odd, integral_cos_pow_zero_pi_odd]
  ring

private theorem expSinSixTerm_integral_even (a : ℝ) (k : ℕ) :
    (∫ θ in (0 : ℝ)..Real.pi,
      Real.sin θ ^ 6 * (a * Real.cos θ) ^ (2 * k) /
        ((2 * k).factorial : ℝ)) =
      (15 * Real.pi / 8) *
        ((a ^ 2 / 4) ^ k /
          ((k.factorial : ℝ) * ((k + 3).factorial : ℝ))) := by
  rw [show (fun θ : ℝ => Real.sin θ ^ 6 * (a * Real.cos θ) ^ (2 * k) /
      ((2 * k).factorial : ℝ)) =
      fun θ => (a ^ (2 * k) / ((2 * k).factorial : ℝ)) *
        (Real.sin θ ^ 6 * Real.cos θ ^ (2 * k)) by
          funext θ
          rw [mul_pow]
          ring]
  rw [intervalIntegral.integral_const_mul, sinSix_even_cos_moment]
  have hfact : (Nat.factorial (2 * k) : ℝ) ≠ 0 := by positivity
  have hden : (Nat.factorial k : ℝ) ≠ 0 := by positivity
  have hden3 : (Nat.factorial (k + 3) : ℝ) ≠ 0 := by positivity
  have hpow : (4 : ℝ) ^ k ≠ 0 := by positivity
  have hunit : (1 / 4 : ℝ) ^ k * 4 ^ k = 1 := by
    rw [← mul_pow]
    norm_num
  field_simp [hfact, hden, hden3, hpow]
  rw [pow_mul]
  rw [div_pow]
  field_simp [hpow]

private theorem expSinSixTerm_integral_odd (a : ℝ) (k : ℕ) :
    (∫ θ in (0 : ℝ)..Real.pi,
      Real.sin θ ^ 6 * (a * Real.cos θ) ^ (2 * k + 1) /
        ((2 * k + 1).factorial : ℝ)) = 0 := by
  rw [show (fun θ : ℝ => Real.sin θ ^ 6 * (a * Real.cos θ) ^ (2 * k + 1) /
      ((2 * k + 1).factorial : ℝ)) =
      fun θ => (a ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)) *
        (Real.sin θ ^ 6 * Real.cos θ ^ (2 * k + 1)) by
          funext θ
          rw [mul_pow]
          ring]
  rw [intervalIntegral.integral_const_mul, sinSix_odd_cos_moment]
  ring

theorem angularSinSixIntegral_eq_besselI3FactorialSeries (a : ℝ) :
    (∫ θ in (0 : ℝ)..Real.pi, Real.sin θ ^ 6 * Real.exp (a * Real.cos θ)) =
      (15 * Real.pi / 8) *
        ∑' n : ℕ, (a ^ 2 / 4) ^ n /
          ((n.factorial : ℝ) * ((n + 3).factorial : ℝ)) := by
  rw [angularSinSixIntegral_eq_tsum,
    tsum_even_odd (summable_expSinSixTerm_integrals a)]
  simp_rw [expSinSixTerm_integral_even, expSinSixTerm_integral_odd]
  simp only [add_zero]
  rw [← tsum_mul_left]

/-- The analytic S⁷ axial angle identity. The coefficient is the standard
order-three modified-Bessel factorial series, with no division by `a`; in
particular the equality is valid at `a = 0`. -/
theorem angularSinSixIntegral_mul_cube_eq_besselI3 (a : ℝ) :
    a ^ 3 * (∫ θ in (0 : ℝ)..Real.pi,
      Real.sin θ ^ 6 * Real.exp (a * Real.cos θ)) =
      15 * Real.pi * besselI3RealSeries a := by
  rw [angularSinSixIntegral_eq_besselI3FactorialSeries, besselI3RealSeries]
  ring

end JinWishart
