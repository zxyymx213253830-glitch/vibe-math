import JinWishartFormalization.BesselI0Angle
import JinWishartFormalization.NoncentralFourDimensionalRadial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Cosine-weighted angular integral for `I₁`

The four-dimensional spherical average reduces to a one-dimensional integral
of `exp (a cos θ) sin² θ`.  Integration by parts turns that into the
cosine-weighted exponential integral proved here, whose value is the `I₁`
series.  The separate sphere-parametrization/Jacobian identity is still needed
to turn this analytic lemma into a probability statement.
-/

open MeasureTheory Set

namespace JinWishart

/-- The `n`th Taylor term of `cos θ * exp (a cos θ)`, as a continuous map. -/
noncomputable def expCosWeightedPowerTerm (a : ℝ) (n : ℕ) : ContinuousMap ℝ ℝ :=
  ⟨fun θ => Real.cos θ * (a * Real.cos θ) ^ n / (n.factorial : ℝ), by fun_prop⟩

/-- Pointwise sum of the weighted Taylor terms. -/
theorem expCosWeightedPowerTerm_tsum (a θ : ℝ) :
    ∑' n : ℕ, expCosWeightedPowerTerm a n θ =
      Real.cos θ * Real.exp (a * Real.cos θ) := by
  calc
    ∑' n : ℕ, expCosWeightedPowerTerm a n θ =
        ∑' n : ℕ, Real.cos θ * expCosPowerTerm a n θ := by
      apply tsum_congr
      intro n
      change Real.cos θ * (a * Real.cos θ) ^ n / (n.factorial : ℝ) =
        Real.cos θ * ((a * Real.cos θ) ^ n / (n.factorial : ℝ))
      ring
    _ = Real.cos θ * ∑' n : ℕ, expCosPowerTerm a n θ := tsum_mul_left
    _ = Real.cos θ * Real.exp (a * Real.cos θ) := by rw [expCosPowerTerm_tsum]

/-- Uniform-norm majorant for the weighted exponential Taylor terms. -/
theorem expCosWeightedPowerTerm_restrict_norm_le (a : ℝ) (n : ℕ) :
    ‖(expCosWeightedPowerTerm a n).restrict
        (⟨uIcc (0 : ℝ) (2 * Real.pi), isCompact_uIcc⟩ :
          TopologicalSpace.Compacts ℝ)‖ ≤ |a| ^ n / (n.factorial : ℝ) := by
  rw [ContinuousMap.norm_le (f := (expCosWeightedPowerTerm a n).restrict
    (⟨uIcc (0 : ℝ) (2 * Real.pi), isCompact_uIcc⟩ :
      TopologicalSpace.Compacts ℝ)) (by positivity)]
  intro θ
  change |Real.cos (θ : ℝ) * (a * Real.cos (θ : ℝ)) ^ n /
    (n.factorial : ℝ)| ≤ _
  have hcos : |Real.cos (θ : ℝ)| ≤ 1 := Real.abs_cos_le_one _
  have hfact : 0 < (n.factorial : ℝ) := by positivity
  rw [abs_div, abs_mul, abs_pow, abs_of_pos hfact, abs_mul, mul_pow]
  calc
    |Real.cos (θ : ℝ)| * (|a| ^ n * |Real.cos (θ : ℝ)| ^ n) /
        (n.factorial : ℝ) ≤ 1 * (|a| ^ n * 1 ^ n) /
          (n.factorial : ℝ) := by
      gcongr
    _ = |a| ^ n / (n.factorial : ℝ) := by ring

/-- The weighted Taylor terms are summable in uniform norm on one full circle. -/
theorem summable_expCosWeightedPowerTerm_restrict_norm (a : ℝ) :
    Summable fun n : ℕ => ‖(expCosWeightedPowerTerm a n).restrict
      (⟨uIcc (0 : ℝ) (2 * Real.pi), isCompact_uIcc⟩ :
        TopologicalSpace.Compacts ℝ)‖ := by
  apply (Real.summable_pow_div_factorial |a|).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact expCosWeightedPowerTerm_restrict_norm_le a n

/-- Sum/integral interchange for the cosine-weighted exponential. -/
theorem angularExpCosIntegral_eq_tsum (a : ℝ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      Real.cos θ * Real.exp (a * Real.cos θ)) =
      ∑' n : ℕ, ∫ θ in (0 : ℝ)..(2 * Real.pi),
        Real.cos θ * (a * Real.cos θ) ^ n / (n.factorial : ℝ) := by
  calc
    _ = ∫ θ in (0 : ℝ)..(2 * Real.pi),
        ∑' n : ℕ, expCosWeightedPowerTerm a n θ := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      exact (expCosWeightedPowerTerm_tsum a θ).symm
    _ = ∑' n : ℕ, ∫ θ in (0 : ℝ)..(2 * Real.pi),
        expCosWeightedPowerTerm a n θ := by
      symm
      exact intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm
        (summable_expCosWeightedPowerTerm_restrict_norm a)
    _ = _ := by
      apply tsum_congr
      intro n
      rfl

/-- A weighted Taylor term is a scalar multiple of a cosine moment. -/
theorem integral_expCosWeightedPowerTerm (a : ℝ) (n : ℕ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      Real.cos θ * (a * Real.cos θ) ^ n / (n.factorial : ℝ)) =
      (a ^ n / (n.factorial : ℝ)) *
        ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.cos θ ^ (n + 1) := by
  have hfun : (fun θ : ℝ =>
      Real.cos θ * (a * Real.cos θ) ^ n / (n.factorial : ℝ)) =
      fun θ => (a ^ n / (n.factorial : ℝ)) * Real.cos θ ^ (n + 1) := by
    funext θ
    rw [mul_pow]
    ring
  rw [hfun, intervalIntegral.integral_const_mul]

/-- Even Taylor indices vanish in the cosine-weighted angular integral. -/
theorem integral_expCosWeightedPowerTerm_even (a : ℝ) (k : ℕ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      Real.cos θ * (a * Real.cos θ) ^ (2 * k) /
        ((2 * k).factorial : ℝ)) = 0 := by
  rw [integral_expCosWeightedPowerTerm, integral_cos_pow_twoPi_odd]
  ring

/-- Odd Taylor indices give exactly the order-one factorial-series term. -/
theorem integral_expCosWeightedPowerTerm_odd (a : ℝ) (k : ℕ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      Real.cos θ * (a * Real.cos θ) ^ (2 * k + 1) /
        ((2 * k + 1).factorial : ℝ)) =
      2 * Real.pi * ((a / 2) * (a ^ 2 / 4) ^ k /
        ((k.factorial : ℝ) * ((k + 1).factorial : ℝ))) := by
  rw [integral_expCosWeightedPowerTerm,
    show 2 * k + 1 + 1 = 2 * (k + 1) by omega,
    integral_cos_pow_twoPi_even]
  have hfact : (Nat.factorial (2 * k + 1) : ℝ) ≠ 0 := by positivity
  have hfact' : (Nat.factorial (2 * (k + 1)) : ℝ) ≠ 0 := by positivity
  have hden : (4 : ℝ) ^ (k + 1) *
      (Nat.factorial (k + 1) : ℝ) ^ 2 ≠ 0 := by positivity
  have hpow : (1 / 4 : ℝ) ^ k * 4 ^ k = 1 := by
    rw [← mul_pow]
    norm_num
  rw [show 2 * (k + 1) = 2 * k + 2 by omega,
    Nat.factorial_succ (2 * k + 1), Nat.factorial_succ (2 * k),
    Nat.factorial_succ k, pow_succ]
  push_cast
  field_simp [Nat.factorial_ne_zero]
  have hpowA : a ^ (2 * k) = (a ^ 2) ^ k := by rw [pow_mul]
  rw [hpowA, div_pow]
  field_simp [pow_ne_zero k (by norm_num : (4 : ℝ) ≠ 0)]
  push_cast
  ring

/-- The scalar series of weighted integrated Taylor terms is summable. -/
theorem summable_expCosWeightedPowerTerm_integrals (a : ℝ) :
    Summable fun n : ℕ =>
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        Real.cos θ * (a * Real.cos θ) ^ n / (n.factorial : ℝ) := by
  apply (Real.summable_pow_div_factorial |a|).mul_left (2 * Real.pi) |>.of_norm_bounded
  intro n
  have hbound : ‖∫ θ in (0 : ℝ)..(2 * Real.pi),
      Real.cos θ * (a * Real.cos θ) ^ n / (n.factorial : ℝ)‖ ≤
      (2 * Real.pi) * (|a| ^ n / (n.factorial : ℝ)) := by
    let C : ℝ := |a| ^ n / (n.factorial : ℝ)
    have hpoint : ∀ θ ∈ uIoc (0 : ℝ) (2 * Real.pi),
        ‖Real.cos θ * (a * Real.cos θ) ^ n /
          (n.factorial : ℝ)‖ ≤ C := by
      intro θ hθ
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow,
        abs_of_pos (by positivity : 0 < (n.factorial : ℝ))]
      dsimp [C]
      have hc : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
      have ha : |a * Real.cos θ| ≤ |a| := by
        rw [abs_mul]
        calc
          |a| * |Real.cos θ| ≤ |a| * 1 := by gcongr
          _ = |a| := by ring
      calc
        |Real.cos θ| * |a * Real.cos θ| ^ n /
            (n.factorial : ℝ) ≤ 1 * |a| ^ n / (n.factorial : ℝ) := by
          gcongr
        _ = |a| ^ n / (n.factorial : ℝ) := by ring
    calc
      _ ≤ (|a| ^ n / (n.factorial : ℝ)) * |(2 * Real.pi) - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hpoint
      _ = (2 * Real.pi) * (|a| ^ n / (n.factorial : ℝ)) := by
        rw [sub_zero, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
        ring
  simpa only [Real.norm_eq_abs] using hbound

/-- The cosine-weighted angular integral is `2π I₁(a)`, expressed using the
real factorial series. -/
theorem angularExpCosIntegral_eq_besselI1RealSeries (a : ℝ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      Real.cos θ * Real.exp (a * Real.cos θ)) =
      2 * Real.pi * besselI1RealSeries a := by
  rw [angularExpCosIntegral_eq_tsum]
  rw [tsum_even_odd (summable_expCosWeightedPowerTerm_integrals a)]
  simp_rw [integral_expCosWeightedPowerTerm_even,
    integral_expCosWeightedPowerTerm_odd]
  simp only [zero_add]
  calc
    _ = 2 * Real.pi * ∑' k : ℕ,
        ((a / 2) * (a ^ 2 / 4) ^ k /
          ((k.factorial : ℝ) * ((k + 1).factorial : ℝ))) := by
      rw [tsum_mul_left]
    _ = 2 * Real.pi * besselI1RealSeries a := by
      unfold besselI1RealSeries
      congr 1
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      ring

/-- Half-circle form of the cosine-weighted angular integral. -/
theorem angularExpCosIntegral_half_eq_pi_besselI1RealSeries (a : ℝ) :
    (∫ θ in (0 : ℝ)..Real.pi,
      Real.cos θ * Real.exp (a * Real.cos θ)) =
      Real.pi * besselI1RealSeries a := by
  let g : ℝ → ℝ := fun θ => Real.cos θ * Real.exp (a * Real.cos θ)
  have hg : Continuous g := by
    change Continuous (fun θ : ℝ => Real.cos θ * Real.exp (a * Real.cos θ))
    fun_prop
  have h01 : IntervalIntegrable g volume 0 Real.pi := hg.intervalIntegrable _ _
  have h12 : IntervalIntegrable g volume Real.pi (2 * Real.pi) :=
    hg.intervalIntegrable _ _
  have hshift : (∫ θ in Real.pi..(2 * Real.pi), g θ) =
      ∫ θ in (0 : ℝ)..Real.pi, g θ := by
    calc
      (∫ θ in Real.pi..(2 * Real.pi), g θ) =
          ∫ θ in Real.pi..(Real.pi + Real.pi), g θ := by
        congr 2 <;> ring
      _ = (∫ θ in (0 : ℝ)..Real.pi, g (θ + Real.pi)) := by
        rw [intervalIntegral.integral_comp_add_right]
        congr 2 <;> ring
      _ = ∫ θ in (0 : ℝ)..Real.pi, g (Real.pi - θ) := by
        apply intervalIntegral.integral_congr
        intro θ hθ
        dsimp [g]
        simp [Real.cos_add, Real.cos_sub]
      _ = ∫ θ in (0 : ℝ)..Real.pi, g θ := by
        rw [intervalIntegral.integral_comp_sub_left]
        simp
  have hadd := intervalIntegral.integral_add_adjacent_intervals h01 h12
  have hfull : (∫ θ in (0 : ℝ)..(2 * Real.pi), g θ) =
      2 * Real.pi * besselI1RealSeries a := by
    simpa [g] using angularExpCosIntegral_eq_besselI1RealSeries a
  rw [hshift, hfull] at hadd
  change (∫ θ in (0 : ℝ)..Real.pi, g θ) = _
  nlinarith

/-- The `sin²` angular moment is `π I₁(a)/a`.  This is the one-dimensional
angular factor appearing in the four-dimensional sphere integral. -/
theorem angularExpSinSqIntegral_eq_pi_besselI1_div (a : ℝ) (ha : a ≠ 0) :
    (∫ θ in (0 : ℝ)..Real.pi,
      Real.exp (a * Real.cos θ) * Real.sin θ ^ 2) =
      Real.pi * besselI1RealSeries a / a := by
  let u : ℝ → ℝ := fun θ => Real.exp (a * Real.cos θ)
  let du : ℝ → ℝ := fun θ => -a * Real.sin θ * Real.exp (a * Real.cos θ)
  let v : ℝ → ℝ := Real.sin
  let dv : ℝ → ℝ := Real.cos
  have hu : ∀ θ ∈ Ioo (min (0 : ℝ) Real.pi) (max 0 Real.pi),
      HasDerivAt u (du θ) θ := by
    intro θ hθ
    have hinner : HasDerivAt (fun x : ℝ => a * Real.cos x)
        (-a * Real.sin θ) θ := by
      convert (Real.hasDerivAt_cos θ).const_mul a using 1 <;> simp <;> ring
    change HasDerivAt (fun x : ℝ => Real.exp (a * Real.cos x))
      (-a * Real.sin θ * Real.exp (a * Real.cos θ)) θ
    convert (Real.hasDerivAt_exp (a * Real.cos θ)).comp θ hinner using 1
    · rfl
    · ring
  have hv : ∀ θ ∈ Ioo (min (0 : ℝ) Real.pi) (max 0 Real.pi),
      HasDerivAt v (dv θ) θ := by
    intro θ hθ
    exact Real.hasDerivAt_sin θ
  have huInt : IntervalIntegrable du volume 0 Real.pi := by
    change IntervalIntegrable
      (fun θ : ℝ => -a * Real.sin θ * Real.exp (a * Real.cos θ)) volume 0 Real.pi
    exact (show Continuous (fun θ : ℝ =>
      -a * Real.sin θ * Real.exp (a * Real.cos θ)) by fun_prop).intervalIntegrable _ _
  have hvInt : IntervalIntegrable dv volume 0 Real.pi := by
    change IntervalIntegrable (fun θ : ℝ => Real.cos θ) volume 0 Real.pi
    exact Real.continuous_cos.intervalIntegrable _ _
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (by
      change ContinuousOn (fun θ : ℝ => Real.exp (a * Real.cos θ)) _
      fun_prop)
    (by
      change ContinuousOn (fun θ : ℝ => Real.sin θ) _
      fun_prop)
    hu hv huInt hvInt
  have hRel :
      (∫ θ in (0 : ℝ)..Real.pi,
        Real.exp (a * Real.cos θ) * Real.cos θ) =
      a * ∫ θ in (0 : ℝ)..Real.pi,
        Real.exp (a * Real.cos θ) * Real.sin θ ^ 2 := by
    calc
      _ = u Real.pi * v Real.pi - u 0 * v 0 -
          ∫ θ in (0 : ℝ)..Real.pi, du θ * v θ := by
        simpa only [u, v, dv, Real.sin_zero, Real.sin_pi] using hIBP
      _ = a * ∫ θ in (0 : ℝ)..Real.pi,
          Real.exp (a * Real.cos θ) * Real.sin θ ^ 2 := by
        simp only [u, du, v, Real.sin_zero, Real.sin_pi]
        rw [show (fun θ : ℝ =>
          (-a * Real.sin θ * Real.exp (a * Real.cos θ)) * Real.sin θ) =
            fun θ => -a * (Real.exp (a * Real.cos θ) * Real.sin θ ^ 2) by
              funext θ
              ring,
          intervalIntegral.integral_const_mul]
        ring
  have hhalf := angularExpCosIntegral_half_eq_pi_besselI1RealSeries a
  have hhalf' :
      (∫ θ in (0 : ℝ)..Real.pi,
        Real.exp (a * Real.cos θ) * Real.cos θ) =
      Real.pi * besselI1RealSeries a := by
    rw [← hhalf]
    apply intervalIntegral.integral_congr
    intro θ hθ
    ring
  rw [hhalf'] at hRel
  field_simp [ha] at hRel ⊢
  nlinarith

end JinWishart
