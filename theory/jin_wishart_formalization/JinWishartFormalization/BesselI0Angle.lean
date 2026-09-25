import JinWishartFormalization.BesselI0Series
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Sets.Compacts

/-!
# Angular integral bridge for the order-zero modified Bessel function

This file develops the cosine moments needed to integrate the exponential
series on a full circle.  It starts with the exact interval recurrence supplied
by Mathlib; the sum/integral interchange is a subsequent obligation.
-/

namespace JinWishart

open Set

/-- The `n`th Taylor term of `exp (a cos θ)`, regarded as a continuous function. -/
noncomputable def expCosPowerTerm (a : ℝ) (n : ℕ) : ContinuousMap ℝ ℝ :=
  ⟨fun θ => (a * Real.cos θ) ^ n / (n.factorial : ℝ), by fun_prop⟩

/-- Pointwise, these continuous terms sum to the ordinary real exponential. -/
theorem expCosPowerTerm_tsum (a θ : ℝ) :
    ∑' n : ℕ, expCosPowerTerm a n θ = Real.exp (a * Real.cos θ) := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
  simp [expCosPowerTerm, smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- Uniform-norm majorant for the exponential Taylor terms on the whole real line. -/
theorem expCosPowerTerm_restrict_norm_le (a : ℝ) (n : ℕ) :
    ‖(expCosPowerTerm a n).restrict
        (⟨uIcc (0 : ℝ) (2 * Real.pi), isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖ ≤
      |a| ^ n / (n.factorial : ℝ) := by
  rw [ContinuousMap.norm_le (f := (expCosPowerTerm a n).restrict
    (⟨uIcc (0 : ℝ) (2 * Real.pi), isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ))
    (by positivity)]
  intro θ
  change |(a * Real.cos (θ : ℝ)) ^ n / (n.factorial : ℝ)| ≤ _
  have hcos : |Real.cos (θ : ℝ)| ≤ 1 := Real.abs_cos_le_one _
  have hfact : 0 < (n.factorial : ℝ) := by positivity
  rw [abs_div, abs_pow, abs_of_pos hfact]
  calc
    |a * Real.cos (θ : ℝ)| ^ n / (n.factorial : ℝ) =
        |a| ^ n * |Real.cos (θ : ℝ)| ^ n / (n.factorial : ℝ) := by
          rw [abs_mul, mul_pow]
    |a| ^ n * |Real.cos (θ : ℝ)| ^ n / (n.factorial : ℝ) ≤
        |a| ^ n * 1 ^ n / (n.factorial : ℝ) := by
          gcongr
    _ = |a| ^ n / (n.factorial : ℝ) := by simp

/-- The Taylor terms are summable in the uniform norm, using Mathlib's
absolute exponential-series majorant. -/
theorem summable_expCosPowerTerm_restrict_norm (a : ℝ) :
    Summable fun n : ℕ => ‖(expCosPowerTerm a n).restrict
      (⟨uIcc (0 : ℝ) (2 * Real.pi), isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖ := by
  apply (Real.summable_pow_div_factorial |a|).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact expCosPowerTerm_restrict_norm_le a n

/-- The angular integral of the exponential is the sum of the integrals of its
Taylor terms.  This is the analytic interchange needed before evaluating the
cosine moments. -/
theorem angularExpIntegral_eq_tsum_cosPowerIntegrals (a : ℝ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.exp (a * Real.cos θ)) =
      ∑' n : ℕ, ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (a * Real.cos θ) ^ n / (n.factorial : ℝ) := by
  calc
    _ = ∫ θ in (0 : ℝ)..(2 * Real.pi), ∑' n : ℕ, expCosPowerTerm a n θ := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      exact (expCosPowerTerm_tsum a θ).symm
    _ = ∑' n : ℕ, ∫ θ in (0 : ℝ)..(2 * Real.pi), expCosPowerTerm a n θ := by
      symm
      exact intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm
        (summable_expCosPowerTerm_restrict_norm a)
    _ = _ := by
      apply tsum_congr
      intro n
      rfl

/-- On a full period, the boundary term in the cosine-power recurrence vanishes. -/
theorem integral_cos_pow_twoPi_succ (n : ℕ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.cos θ ^ (n + 2)) =
      ((n + 1 : ℝ) / (n + 2)) *
        ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.cos θ ^ n := by
  rw [integral_cos_pow]
  simp

/-- Odd cosine moments vanish over a full period. -/
theorem integral_cos_pow_twoPi_odd (k : ℕ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.cos θ ^ (2 * k + 1)) = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega,
        integral_cos_pow_twoPi_succ]
      rw [ih]
      ring

/-- Even cosine moments over a full period, in factorial form. -/
theorem integral_cos_pow_twoPi_even (k : ℕ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.cos θ ^ (2 * k)) =
      2 * Real.pi * ((Nat.factorial (2 * k) : ℝ) /
        (4 ^ k * (Nat.factorial k : ℝ) ^ 2)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 2 by omega,
        integral_cos_pow_twoPi_succ, ih]
      rw [Nat.factorial_succ (2 * k + 1), Nat.factorial_succ (2 * k),
        Nat.factorial_succ k, pow_succ]
      push_cast
      field_simp [Nat.factorial_ne_zero]
      ring

/-- Reindexing a natural-number series by quotient and remainder modulo two
splits it into its even and odd terms. -/
theorem tsum_even_odd {f : ℕ → ℝ} (hf : Summable f) :
    ∑' n : ℕ, f n = ∑' k : ℕ, (f (2 * k) + f (2 * k + 1)) := by
  let e := Nat.divModEquiv 2
  have hp := e.symm.hasSum_iff.mpr hf.hasSum
  have hfiber : ∀ k : ℕ,
      HasSum (fun r : Fin 2 => f (e.symm (k, r)))
        (f (2 * k) + f (2 * k + 1)) := by
    intro k
    convert hasSum_fintype (fun r : Fin 2 => f (e.symm (k, r))) using 1
    simp [e, Nat.divModEquiv_symm_apply, Fin.sum_univ_two, Nat.mul_comm]
  have hsplit := hp.prod_fiberwise hfiber
  calc
    ∑' n : ℕ, f n = _ := hp.tsum_eq.symm
    _ = ∑' k : ℕ, (f (2 * k) + f (2 * k + 1)) := by
      calc
        ∑' p : ℕ × Fin 2, f (e.symm p) = ∑' b : ℕ, f b := hp.tsum_eq
        _ = ∑' k : ℕ, (f (2 * k) + f (2 * k + 1)) := hsplit.tsum_eq.symm

/-- The integrated `n`th exponential Taylor term is uniformly dominated by a
constant multiple of the scalar exponential-series majorant. -/
theorem expCosPowerIntegral_norm_le (a : ℝ) (n : ℕ) :
    ‖∫ θ in (0 : ℝ)..(2 * Real.pi),
      (a * Real.cos θ) ^ n / (n.factorial : ℝ)‖ ≤
      (2 * Real.pi) * (|a| ^ n / (n.factorial : ℝ)) := by
  let C : ℝ := |a| ^ n / (n.factorial : ℝ)
  have hpoint : ∀ θ ∈ uIoc (0 : ℝ) (2 * Real.pi),
      ‖(a * Real.cos θ) ^ n / (n.factorial : ℝ)‖ ≤ C := by
    intro θ hθ
    rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos (by positivity :
      0 < (n.factorial : ℝ))]
    dsimp [C]
    have hcos : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
    calc
      |a * Real.cos θ| ^ n / (n.factorial : ℝ) =
          |a| ^ n * |Real.cos θ| ^ n / (n.factorial : ℝ) := by
            rw [abs_mul, mul_pow]
      _ ≤ |a| ^ n * 1 ^ n / (n.factorial : ℝ) := by gcongr
      _ = |a| ^ n / (n.factorial : ℝ) := by simp
  calc
    _ ≤ (|a| ^ n / (n.factorial : ℝ)) * |(2 * Real.pi) - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ = (2 * Real.pi) * (|a| ^ n / (n.factorial : ℝ)) := by
      rw [sub_zero, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      ring

/-- The scalar series of integrated Taylor terms is summable. -/
theorem summable_expCosPowerIntegrals (a : ℝ) :
    Summable fun n : ℕ =>
      ∫ θ in (0 : ℝ)..(2 * Real.pi), (a * Real.cos θ) ^ n / (n.factorial : ℝ) := by
  apply (Real.summable_pow_div_factorial |a|).mul_left (2 * Real.pi) |>.of_norm_bounded
  intro n
  simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
    expCosPowerIntegral_norm_le a n

/-- Integration of a single Taylor term reduces exactly to its cosine moment. -/
theorem integral_expCosPowerTerm (a : ℝ) (n : ℕ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (a * Real.cos θ) ^ n / (n.factorial : ℝ)) =
      (a ^ n / (n.factorial : ℝ)) *
        ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.cos θ ^ n := by
  have hfun : (fun θ : ℝ => (a * Real.cos θ) ^ n / (n.factorial : ℝ)) =
      fun θ => (a ^ n / (n.factorial : ℝ)) * Real.cos θ ^ n := by
    funext θ
    rw [mul_pow]
    ring
  rw [hfun, intervalIntegral.integral_const_mul]

/-- Odd integrated exponential Taylor terms vanish. -/
theorem integral_expCosPowerTerm_odd (a : ℝ) (k : ℕ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (a * Real.cos θ) ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)) = 0 := by
  rw [integral_expCosPowerTerm, integral_cos_pow_twoPi_odd]
  ring

/-- Even integrated exponential Taylor terms have the factorial-series
coefficients defining the order-zero modified Bessel function. -/
theorem integral_expCosPowerTerm_even (a : ℝ) (k : ℕ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      (a * Real.cos θ) ^ (2 * k) / ((2 * k).factorial : ℝ)) =
      2 * Real.pi * ((a ^ 2 / 4) ^ k / ((k.factorial : ℝ) ^ 2)) := by
  rw [integral_expCosPowerTerm, integral_cos_pow_twoPi_even]
  have hfact : (Nat.factorial (2 * k) : ℝ) ≠ 0 := by positivity
  have hden : (4 : ℝ) ^ k * (Nat.factorial k : ℝ) ^ 2 ≠ 0 := by positivity
  field_simp [hfact, hden]
  rw [← mul_pow, show 4 * (a ^ 2 / 4) = a ^ 2 by field_simp]
  exact pow_mul a 2 k

/-- The full-circle exponential integral is the factorial series for `I₀` times
the circle length. -/
theorem angularExpIntegral_eq_factorialSeries (a : ℝ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.exp (a * Real.cos θ)) =
      2 * Real.pi * ∑' k : ℕ, (a ^ 2 / 4) ^ k / ((k.factorial : ℝ) ^ 2) := by
  rw [angularExpIntegral_eq_tsum_cosPowerIntegrals]
  rw [tsum_even_odd (summable_expCosPowerIntegrals a)]
  simp_rw [integral_expCosPowerTerm_odd, integral_expCosPowerTerm_even]
  simp only [add_zero]
  rw [tsum_mul_left]

/-- The full-circle angular integral is `2π I₀(a)`, with the real argument
embedded into the complex domain used by the library's modified Bessel
function. -/
theorem angularExpIntegral_eq_modifiedBesselI_zero (a : ℝ) :
    ((∫ θ in (0 : ℝ)..(2 * Real.pi), Real.exp (a * Real.cos θ) : ℝ) : ℂ) =
      ((2 * Real.pi : ℝ) : ℂ) * modifiedBesselI 0 (a : ℂ) := by
  calc
    ((∫ θ in (0 : ℝ)..(2 * Real.pi), Real.exp (a * Real.cos θ) : ℝ) : ℂ) =
        (((2 * Real.pi) *
          ∑' k : ℕ, (a ^ 2 / 4) ^ k / ((k.factorial : ℝ) ^ 2) : ℝ) : ℂ) := by
          rw [angularExpIntegral_eq_factorialSeries]
    _ = ((2 * Real.pi : ℝ) : ℂ) *
        (((∑' k : ℕ, (a ^ 2 / 4) ^ k / ((k.factorial : ℝ) ^ 2)) : ℝ) : ℂ) := by
          exact Complex.ofReal_mul _ _
    _ = ((2 * Real.pi : ℝ) : ℂ) * modifiedBesselI 0 (a : ℂ) := by
          rw [modifiedBesselI_zero_ofReal_eq_realSeries]

/-- The normalized angular average is exactly the order-zero modified Bessel
function, in the complex embedding used by Mathlib. -/
theorem angularAverage_eq_modifiedBesselI_zero (a : ℝ) :
    ((((2 * Real.pi)⁻¹ *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.exp (a * Real.cos θ) : ℝ) : ℝ) : ℂ) =
        modifiedBesselI 0 (a : ℂ) := by
  calc
    ((((2 * Real.pi)⁻¹ *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.exp (a * Real.cos θ) : ℝ) : ℝ) : ℂ) =
        (((∑' k : ℕ, (a ^ 2 / 4) ^ k / ((k.factorial : ℝ) ^ 2)) : ℝ) : ℂ) := by
          congr 1
          rw [angularExpIntegral_eq_factorialSeries]
          have hpi : 2 * Real.pi ≠ 0 := by positivity
          field_simp
    _ = modifiedBesselI 0 (a : ℂ) :=
      modifiedBesselI_zero_ofReal_eq_realSeries a

end JinWishart
