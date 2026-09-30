import JinWishartFormalization.BesselI0Angle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Sets.Compacts

/-!
# Six-dimensional axial angular integral and the order-two Bessel series

The analytic one-dimensional identity needed for the `S⁵` shell integral is
isolated here.  The conversion of the actual geometric `toSphere` measure on
`S⁵` to this one-dimensional angle chart is a separate measure-geometry step.
-/

namespace JinWishart

open MeasureTheory Set

/-- Real factorial series for modified Bessel `I₂`. -/
noncomputable def besselI2RealSeries (a : ℝ) : ℝ :=
  (a ^ 2 / 4) * ∑' n : ℕ,
    (a ^ 2 / 4) ^ n / ((n.factorial : ℝ) * ((n + 2).factorial : ℝ))

/-- The Taylor summand for the `sin⁴`-weighted axial exponential integral. -/
noncomputable def expCosSinFourTerm (a : ℝ) (n : ℕ) : ContinuousMap ℝ ℝ :=
  ⟨fun θ => Real.sin θ ^ 4 * (a * Real.cos θ) ^ n / (n.factorial : ℝ), by fun_prop⟩

theorem expCosSinFourTerm_tsum (a θ : ℝ) :
    ∑' n : ℕ, expCosSinFourTerm a n θ =
      Real.sin θ ^ 4 * Real.exp (a * Real.cos θ) := by
  calc
    ∑' n : ℕ, expCosSinFourTerm a n θ =
        ∑' n : ℕ, Real.sin θ ^ 4 * expCosPowerTerm a n θ := by
      apply tsum_congr
      intro n
      change Real.sin θ ^ 4 * (a * Real.cos θ) ^ n / (n.factorial : ℝ) =
        Real.sin θ ^ 4 * ((a * Real.cos θ) ^ n / (n.factorial : ℝ))
      ring
    _ = Real.sin θ ^ 4 * ∑' n : ℕ, expCosPowerTerm a n θ := tsum_mul_left
    _ = _ := by rw [expCosPowerTerm_tsum]

theorem expCosSinFourTerm_restrict_norm_le (a : ℝ) (n : ℕ) :
    ‖(expCosSinFourTerm a n).restrict
      (⟨uIcc (0 : ℝ) Real.pi, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖ ≤
      |a| ^ n / (n.factorial : ℝ) := by
  rw [ContinuousMap.norm_le (f := (expCosSinFourTerm a n).restrict
    (⟨uIcc (0 : ℝ) Real.pi, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ))
    (by positivity : 0 ≤ |a| ^ n / (n.factorial : ℝ))]
  intro θ
  change |Real.sin (θ : ℝ) ^ 4 * (a * Real.cos (θ : ℝ)) ^ n /
    (n.factorial : ℝ)| ≤ _
  have hs : |Real.sin (θ : ℝ)| ≤ 1 := Real.abs_sin_le_one _
  have hc : |Real.cos (θ : ℝ)| ≤ 1 := Real.abs_cos_le_one _
  have hf : 0 < (n.factorial : ℝ) := by positivity
  rw [abs_div, abs_mul, abs_pow, abs_of_pos hf, abs_pow, abs_mul]
  calc
    |Real.sin (θ : ℝ)| ^ 4 * (|a| * |Real.cos (θ : ℝ)|) ^ n /
        (n.factorial : ℝ) ≤ 1 ^ 4 * (|a| * 1) ^ n / (n.factorial : ℝ) := by
          gcongr
    _ = |a| ^ n / (n.factorial : ℝ) := by simp

theorem summable_expCosSinFourTerm_restrict_norm (a : ℝ) :
    Summable fun n : ℕ => ‖(expCosSinFourTerm a n).restrict
      (⟨uIcc (0 : ℝ) Real.pi, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖ := by
  apply (Real.summable_pow_div_factorial |a|).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact expCosSinFourTerm_restrict_norm_le a n

/-- Interchange the uniformly summable exponential Taylor series and the
compact interval integral. -/
theorem angularSinFourIntegral_eq_tsum (a : ℝ) :
    (∫ θ in (0 : ℝ)..Real.pi, Real.sin θ ^ 4 * Real.exp (a * Real.cos θ)) =
      ∑' n : ℕ, ∫ θ in (0 : ℝ)..Real.pi,
        Real.sin θ ^ 4 * (a * Real.cos θ) ^ n / (n.factorial : ℝ) := by
  calc
    _ = ∫ θ in (0 : ℝ)..Real.pi,
        ∑' n : ℕ, expCosSinFourTerm a n θ := by
      apply intervalIntegral.integral_congr
      intro θ _
      exact (expCosSinFourTerm_tsum a θ).symm
    _ = ∑' n : ℕ, ∫ θ in (0 : ℝ)..Real.pi, expCosSinFourTerm a n θ := by
      symm
      exact intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm
        (summable_expCosSinFourTerm_restrict_norm a)
    _ = _ := by
      apply tsum_congr
      intro n
      rfl

private theorem expSinFourIntegral_norm_le (a : ℝ) (n : ℕ) :
    ‖∫ θ in (0 : ℝ)..Real.pi,
      Real.sin θ ^ 4 * (a * Real.cos θ) ^ n / (n.factorial : ℝ)‖ ≤
        Real.pi * (|a| ^ n / (n.factorial : ℝ)) := by
  let C : ℝ := |a| ^ n / (n.factorial : ℝ)
  have hpoint : ∀ θ ∈ uIoc (0 : ℝ) Real.pi,
      ‖Real.sin θ ^ 4 * (a * Real.cos θ) ^ n /
        (n.factorial : ℝ)‖ ≤ C := by
    intro θ hθ
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow,
      abs_of_pos (by positivity : 0 < (n.factorial : ℝ)), abs_pow, abs_mul]
    dsimp [C]
    have hs : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one _
    have hc : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one _
    calc
      |Real.sin θ| ^ 4 * (|a| * |Real.cos θ|) ^ n /
          (n.factorial : ℝ) ≤ 1 ^ 4 * (|a| * 1) ^ n /
            (n.factorial : ℝ) := by gcongr
      _ = |a| ^ n / (n.factorial : ℝ) := by simp
  calc
    _ ≤ (|a| ^ n / (n.factorial : ℝ)) * |Real.pi - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ = Real.pi * (|a| ^ n / (n.factorial : ℝ)) := by
      rw [sub_zero, abs_of_pos Real.pi_pos]
      ring

private theorem summable_expCosSinFourTerm_integrals (a : ℝ) :
    Summable fun n : ℕ => ∫ θ in (0 : ℝ)..Real.pi,
      Real.sin θ ^ 4 * (a * Real.cos θ) ^ n / (n.factorial : ℝ) := by
  apply (Real.summable_pow_div_factorial |a|).mul_left Real.pi |>.of_norm_bounded
  intro n
  simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
    expSinFourIntegral_norm_le a n

/-- Cosine moments on a half-turn; odd powers vanish and even powers have
the usual factorial value. -/
theorem integral_cos_pow_zero_pi_even (k : ℕ) :
    (∫ θ in (0 : ℝ)..Real.pi, Real.cos θ ^ (2 * k)) =
      Real.pi * ((Nat.factorial (2 * k) : ℝ) /
        (4 ^ k * (Nat.factorial k : ℝ) ^ 2)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 2 by omega, integral_cos_pow, ih]
      simp only [Real.cos_zero, Real.cos_pi, Real.sin_zero, Real.sin_pi,
        zero_pow (by omega : 2 * k + 1 ≠ 0), mul_zero, sub_zero, zero_sub,
        neg_zero, add_zero]
      rw [Nat.factorial_succ (2 * k + 1), Nat.factorial_succ (2 * k),
        Nat.factorial_succ k, pow_succ]
      push_cast
      field_simp [Nat.factorial_ne_zero]
      ring

theorem integral_cos_pow_zero_pi_odd (k : ℕ) :
    (∫ θ in (0 : ℝ)..Real.pi, Real.cos θ ^ (2 * k + 1)) = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega,
        integral_cos_pow]
      simp only [Real.cos_zero, Real.cos_pi, Real.sin_zero, Real.sin_pi,
        zero_pow (by omega : 2 * k + 2 ≠ 0), mul_zero, sub_zero, zero_sub,
        neg_zero, add_zero]
      rw [ih]
      ring

private theorem sinFour_even_cos_moment (k : ℕ) :
    (∫ θ in (0 : ℝ)..Real.pi,
      Real.sin θ ^ 4 * Real.cos θ ^ (2 * k)) =
      (3 * Real.pi / 4) *
        ((Nat.factorial (2 * k) : ℝ) /
          (4 ^ k * (Nat.factorial k : ℝ) * (Nat.factorial (k + 2) : ℝ))) := by
  have hsin : ∀ θ : ℝ, Real.sin θ ^ 4 * Real.cos θ ^ (2 * k) =
      Real.cos θ ^ (2 * k) - 2 * Real.cos θ ^ (2 * k + 2) +
        Real.cos θ ^ (2 * k + 4) := by
    intro θ
    have hs : Real.sin θ ^ 4 = (1 - Real.cos θ ^ 2) ^ 2 := by
      calc
        Real.sin θ ^ 4 = (Real.sin θ ^ 2) ^ 2 := by ring
        _ = (1 - Real.cos θ ^ 2) ^ 2 := by rw [Real.sin_sq]
    rw [hs]
    ring
  have hInt (j : ℕ) : IntervalIntegrable (fun θ : ℝ => Real.cos θ ^ j)
      volume 0 Real.pi := (Real.continuous_cos.pow j).intervalIntegrable _ _
  rw [show (fun θ : ℝ => Real.sin θ ^ 4 * Real.cos θ ^ (2 * k)) =
      fun θ => Real.cos θ ^ (2 * k) - 2 * Real.cos θ ^ (2 * k + 2) +
        Real.cos θ ^ (2 * k + 4) by
          funext θ; exact hsin θ]
  have hscaled : IntervalIntegrable
      (fun θ : ℝ => (2 : ℝ) * Real.cos θ ^ (2 * k + 2)) volume 0 Real.pi :=
    (hInt _).const_mul 2
  rw [intervalIntegral.integral_add ((hInt _).sub hscaled) (hInt _),
    intervalIntegral.integral_sub (hInt _) hscaled,
    intervalIntegral.integral_const_mul]
  rw [show 2 * k + 2 = 2 * (k + 1) by omega,
    show 2 * k + 4 = 2 * (k + 2) by omega,
    integral_cos_pow_zero_pi_even, integral_cos_pow_zero_pi_even,
    integral_cos_pow_zero_pi_even]
  push_cast
  rw [show 2 * (k + 1) = 2 * k + 2 by omega,
    show 2 * (k + 2) = 2 * k + 4 by omega]
  have hf0 : (Nat.factorial k : ℝ) ≠ 0 := by positivity
  have hf2 : (Nat.factorial (k + 2) : ℝ) ≠ 0 := by positivity
  have hp : (4 : ℝ) ^ k ≠ 0 := by positivity
  rw [Nat.factorial_succ (2 * k + 3), Nat.factorial_succ (2 * k + 2),
    Nat.factorial_succ (2 * k + 1), Nat.factorial_succ (2 * k),
    Nat.factorial_succ (k + 1), Nat.factorial_succ k]
  simp only [pow_succ]
  push_cast
  field_simp [hf0, hf2, hp]
  <;> ring_nf

private theorem sinFour_odd_cos_moment (k : ℕ) :
    (∫ θ in (0 : ℝ)..Real.pi,
      Real.sin θ ^ 4 * Real.cos θ ^ (2 * k + 1)) = 0 := by
  have hsin : ∀ θ : ℝ, Real.sin θ ^ 4 * Real.cos θ ^ (2 * k + 1) =
      Real.cos θ ^ (2 * k + 1) - 2 * Real.cos θ ^ (2 * k + 3) +
        Real.cos θ ^ (2 * k + 5) := by
    intro θ
    have hs : Real.sin θ ^ 4 = (1 - Real.cos θ ^ 2) ^ 2 := by
      calc
        Real.sin θ ^ 4 = (Real.sin θ ^ 2) ^ 2 := by ring
        _ = (1 - Real.cos θ ^ 2) ^ 2 := by rw [Real.sin_sq]
    rw [hs]
    ring
  rw [show (fun θ : ℝ => Real.sin θ ^ 4 * Real.cos θ ^ (2 * k + 1)) =
      fun θ => Real.cos θ ^ (2 * k + 1) - 2 * Real.cos θ ^ (2 * k + 3) +
        Real.cos θ ^ (2 * k + 5) by
          funext θ; exact hsin θ]
  have h1 : IntervalIntegrable (fun θ : ℝ => Real.cos θ ^ (2 * k + 1))
      volume 0 Real.pi := (Real.continuous_cos.pow _).intervalIntegrable _ _
  have h3 : IntervalIntegrable (fun θ : ℝ => Real.cos θ ^ (2 * k + 3))
      volume 0 Real.pi := (Real.continuous_cos.pow _).intervalIntegrable _ _
  have h5 : IntervalIntegrable (fun θ : ℝ => Real.cos θ ^ (2 * k + 5))
      volume 0 Real.pi := (Real.continuous_cos.pow _).intervalIntegrable _ _
  have hscaled : IntervalIntegrable
      (fun θ : ℝ => (2 : ℝ) * Real.cos θ ^ (2 * k + 3)) volume 0 Real.pi :=
    h3.const_mul 2
  rw [intervalIntegral.integral_add (h1.sub hscaled) h5,
    intervalIntegral.integral_sub h1 hscaled,
    intervalIntegral.integral_const_mul]
  rw [show 2 * k + 3 = 2 * (k + 1) + 1 by omega,
    show 2 * k + 5 = 2 * (k + 2) + 1 by omega,
    integral_cos_pow_zero_pi_odd, integral_cos_pow_zero_pi_odd,
    integral_cos_pow_zero_pi_odd]
  ring

private theorem expSinFourTerm_integral_even (a : ℝ) (k : ℕ) :
    (∫ θ in (0 : ℝ)..Real.pi,
      Real.sin θ ^ 4 * (a * Real.cos θ) ^ (2 * k) /
        ((2 * k).factorial : ℝ)) =
      (3 * Real.pi / 4) *
        ((a ^ 2 / 4) ^ k /
          ((k.factorial : ℝ) * ((k + 2).factorial : ℝ))) := by
  rw [show (fun θ : ℝ => Real.sin θ ^ 4 * (a * Real.cos θ) ^ (2 * k) /
      ((2 * k).factorial : ℝ)) =
      fun θ => (a ^ (2 * k) / ((2 * k).factorial : ℝ)) *
        (Real.sin θ ^ 4 * Real.cos θ ^ (2 * k)) by
          funext θ
          rw [mul_pow]
          ring]
  rw [intervalIntegral.integral_const_mul, sinFour_even_cos_moment]
  have hfact : (Nat.factorial (2 * k) : ℝ) ≠ 0 := by positivity
  have hden : (Nat.factorial k : ℝ) ≠ 0 := by positivity
  have hden2 : (Nat.factorial (k + 2) : ℝ) ≠ 0 := by positivity
  have hpow : (4 : ℝ) ^ k ≠ 0 := by positivity
  have hunit : (1 / 4 : ℝ) ^ k * 4 ^ k = 1 := by
    rw [← mul_pow]
    norm_num
  field_simp [hfact, hden, hden2, hpow]
  rw [pow_mul]
  rw [div_pow]
  field_simp [hpow]

private theorem expSinFourTerm_integral_odd (a : ℝ) (k : ℕ) :
    (∫ θ in (0 : ℝ)..Real.pi,
      Real.sin θ ^ 4 * (a * Real.cos θ) ^ (2 * k + 1) /
        ((2 * k + 1).factorial : ℝ)) = 0 := by
  rw [show (fun θ : ℝ => Real.sin θ ^ 4 * (a * Real.cos θ) ^ (2 * k + 1) /
      ((2 * k + 1).factorial : ℝ)) =
      fun θ => (a ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)) *
        (Real.sin θ ^ 4 * Real.cos θ ^ (2 * k + 1)) by
          funext θ
          rw [mul_pow]
          ring]
  rw [intervalIntegral.integral_const_mul, sinFour_odd_cos_moment]
  ring

theorem angularSinFourIntegral_eq_besselI2Series (a : ℝ) :
    (∫ θ in (0 : ℝ)..Real.pi, Real.sin θ ^ 4 * Real.exp (a * Real.cos θ)) =
      (3 * Real.pi / 4) *
        ∑' n : ℕ, (a ^ 2 / 4) ^ n /
          ((n.factorial : ℝ) * ((n + 2).factorial : ℝ)) := by
  rw [angularSinFourIntegral_eq_tsum,
    tsum_even_odd (summable_expCosSinFourTerm_integrals a)]
  simp_rw [expSinFourTerm_integral_even, expSinFourTerm_integral_odd]
  simp only [add_zero]
  rw [← tsum_mul_left]

/-- The `S⁵` one-angle integral equals `3π I₂(a)/a²`; the denominator-free
form remains valid at `a=0`. -/
theorem angularSinFourIntegral_mul_sq_eq_besselI2 (a : ℝ) :
    a ^ 2 * (∫ θ in (0 : ℝ)..Real.pi,
      Real.sin θ ^ 4 * Real.exp (a * Real.cos θ)) =
      3 * Real.pi * besselI2RealSeries a := by
  rw [angularSinFourIntegral_eq_besselI2Series, besselI2RealSeries]
  ring

/-- The axial slice weight on `[-1,1]`. For `u ∈ [-1,1]`, the square-root
form is exactly `(1-u²)^(3/2)` and remains continuous at the endpoints. -/
noncomputable def axialSixDimensionalWeight (a u : ℝ) : ℝ :=
  Real.exp (a * u) * Real.sqrt (1 - u ^ 2) ^ 3

/-- The six-dimensional axial slice integral is the `sin⁴` one-angle integral.
This is the analytic substitution `u = cos θ`; it does not yet identify the
angle chart with Mathlib's geometric measure on `S⁵`. -/
theorem axialSixDimensionalIntegral_eq_angularSinFour (a : ℝ) :
    (∫ u in (-1 : ℝ)..1, axialSixDimensionalWeight a u) =
      ∫ θ in (0 : ℝ)..Real.pi,
        Real.sin θ ^ 4 * Real.exp (a * Real.cos θ) := by
  let g : ℝ → ℝ := axialSixDimensionalWeight a
  have hg : Continuous g := by
    change Continuous (fun u : ℝ =>
      Real.exp (a * u) * Real.sqrt (1 - u ^ 2) ^ 3)
    fun_prop
  have hsub := intervalIntegral.integral_comp_mul_deriv
    (a := (0 : ℝ)) (b := Real.pi) (f := Real.cos)
    (f' := fun θ => -Real.sin θ) (g := g)
    (fun θ _ => Real.hasDerivAt_cos θ)
    Real.continuousOn_sin.neg hg
  have hcos0 : Real.cos 0 = 1 := by simp
  have hcosπ : Real.cos Real.pi = -1 := by simp
  rw [hcos0, hcosπ] at hsub
  have hpoint : ∀ θ ∈ uIcc (0 : ℝ) Real.pi,
      (g ∘ Real.cos) θ * (-Real.sin θ) =
        -(Real.sin θ ^ 4 * Real.exp (a * Real.cos θ)) := by
    intro θ hθ
    have hθ' : θ ∈ Set.Icc 0 Real.pi := by
      simpa [uIcc_of_le Real.pi_pos.le] using hθ
    have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc hθ'
    have hsq : 1 - Real.cos θ ^ 2 = Real.sin θ ^ 2 := by
      rw [Real.sin_sq]
    dsimp [g, axialSixDimensionalWeight]
    rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg hs]
    ring
  have hcomp : (∫ θ in (0 : ℝ)..Real.pi,
      (g ∘ Real.cos) θ * (-Real.sin θ)) =
        -(∫ θ in (0 : ℝ)..Real.pi,
          Real.sin θ ^ 4 * Real.exp (a * Real.cos θ)) := by
    calc
      _ = ∫ θ in (0 : ℝ)..Real.pi,
          -(Real.sin θ ^ 4 * Real.exp (a * Real.cos θ)) := by
        apply intervalIntegral.integral_congr
        intro θ hθ
        exact hpoint θ hθ
      _ = _ := by rw [intervalIntegral.integral_neg]
  calc
    _ = -(∫ u in (1 : ℝ)..(-1 : ℝ), g u) := by
      rw [intervalIntegral.integral_symm]
    _ = -(∫ θ in (0 : ℝ)..Real.pi,
        (g ∘ Real.cos) θ * (-Real.sin θ)) := by rw [hsub]
    _ = ∫ θ in (0 : ℝ)..Real.pi,
        Real.sin θ ^ 4 * Real.exp (a * Real.cos θ) := by rw [hcomp]; ring

/-- Exact one-dimensional S⁵ axial integral in the order-two modified-Bessel
factorial series. This also holds at `a=0` without dividing by `a²`. -/
theorem axialSixDimensionalIntegral_eq_besselI2Series (a : ℝ) :
    (∫ u in (-1 : ℝ)..1, axialSixDimensionalWeight a u) =
      (3 * Real.pi / 4) *
        ∑' n : ℕ, (a ^ 2 / 4) ^ n /
          ((n.factorial : ℝ) * ((n + 2).factorial : ℝ)) := by
  rw [axialSixDimensionalIntegral_eq_angularSinFour,
    angularSinFourIntegral_eq_besselI2Series]

/-- The requested `(1-u²)^(3/2)` notation agrees with the continuous
square-root weight on the integration interval. -/
theorem axialSixDimensionalWeight_eq_rpow {a u : ℝ} (hu : u ∈ Set.Icc (-1) 1) :
    axialSixDimensionalWeight a u =
      Real.exp (a * u) * (1 - u ^ 2) ^ (3 / (2 : ℝ)) := by
  have hbase : 0 ≤ 1 - u ^ 2 := by
    nlinarith [hu.1, hu.2, sq_nonneg u]
  rw [axialSixDimensionalWeight, Real.rpow_div_two_eq_sqrt 3 hbase]
  exact congrArg (fun z : ℝ => Real.exp (a * u) * z)
    (Real.rpow_natCast (Real.sqrt (1 - u ^ 2)) 3).symm

/-- Direct `(1-u²)^(3/2)` form of the exact order-two series integral. -/
theorem axialSixDimensionalRpowIntegral_eq_besselI2Series (a : ℝ) :
    (∫ u in (-1 : ℝ)..1,
      Real.exp (a * u) * (1 - u ^ 2) ^ (3 / (2 : ℝ))) =
      (3 * Real.pi / 4) *
        ∑' n : ℕ, (a ^ 2 / 4) ^ n /
          ((n.factorial : ℝ) * ((n + 2).factorial : ℝ)) := by
  calc
    _ = ∫ u in (-1 : ℝ)..1, axialSixDimensionalWeight a u := by
      apply intervalIntegral.integral_congr
      intro u hu
      have hu' : u ∈ Set.Icc (-1) 1 := by
        simpa [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hu
      exact (axialSixDimensionalWeight_eq_rpow hu').symm
    _ = _ := axialSixDimensionalIntegral_eq_besselI2Series a

end JinWishart
