import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Incomplete Gamma recurrence used by the Wishart eigenvalue formulas

Mathlib provides the complete Gamma integral and the lower incomplete Gamma
integral together with integration-by-parts recurrences.  We prove that their
algebraic complement is the improper tail integral on `(x, ∞)` for `x ≥ 0`,
then derive the integer-shape finite-sum expression.
-/

namespace JinWishart

open MeasureTheory Set

/-- Algebraic complement of the lower incomplete Gamma integral. -/
noncomputable def upperGammaComplement (s : ℂ) (x : ℝ) : ℂ :=
  Complex.GammaIntegral s - Complex.partialGamma s x

/-- The improper upper-tail integral for the Gamma density. -/
noncomputable def upperGammaTail (s : ℂ) (x : ℝ) : ℂ :=
  ∫ t in Set.Ioi x, (-t).exp * t ^ (s - 1)

@[simp]
theorem partialGamma_zero (s : ℂ) : Complex.partialGamma s 0 = 0 := by
  simp [Complex.partialGamma]

/-- For nonnegative thresholds, the algebraic complement is exactly the upper-tail
integral. This uses only additivity of the Bochner integral over adjacent intervals. -/
theorem upperGammaComplement_eq_tail {s : ℂ} (hs : 0 < s.re)
    {x : ℝ} (hx : 0 ≤ x) :
    upperGammaComplement s x = upperGammaTail s x := by
  let f : ℝ → ℂ := fun t => (-t).exp * t ^ (s - 1)
  have h0 : IntegrableOn f (Set.Ioi 0) := by
    simpa [f, Complex.GammaIntegral] using Complex.GammaIntegral_convergent hs
  have hxint : IntegrableOn f (Set.Ioi x) :=
    h0.mono_set (Set.Ioi_subset_Ioi hx)
  have hsplit := intervalIntegral.integral_interval_add_Ioi (f := f) h0 hxint
  rw [upperGammaComplement, upperGammaTail, Complex.GammaIntegral,
    Complex.partialGamma]
  apply sub_eq_iff_eq_add.mpr
  simpa [f, add_comm] using hsplit.symm

/-- The complement satisfies the standard upper incomplete Gamma recurrence.
The restriction `x ≥ 0` is inherited from mathlib's lower-Gamma recurrence. -/
theorem upperGammaComplement_add_one {s : ℂ} (hs : 0 < s.re)
    {x : ℝ} (hx : 0 ≤ x) :
    upperGammaComplement (s + 1) x =
      s * upperGammaComplement s x + (-x).exp * x ^ s := by
  rw [upperGammaComplement, upperGammaComplement,
    Complex.GammaIntegral_add_one hs, Complex.partialGamma_add_one hs hx]
  ring

/-- The lower incomplete Gamma integral at shape one. -/
theorem partialGamma_one (x : ℝ) :
    Complex.partialGamma 1 x = ((1 - Real.exp (-x) : ℝ) : ℂ) := by
  rw [Complex.partialGamma]
  have hfun :
      (fun t : ℝ => (Real.exp (-t) : ℂ) *
        (t : ℂ) ^ ((1 : ℂ) - 1)) =
        (fun t : ℝ => Complex.exp ((-1 : ℂ) * t)) := by
    funext t
    simp
  rw [hfun, integral_exp_mul_complex (by norm_num : (-1 : ℂ) ≠ 0)]
  simp
  ring

/-- Boundary value of the complementary incomplete Gamma at shape one. -/
theorem upperGammaComplement_one (x : ℝ) :
    upperGammaComplement 1 x = ((Real.exp (-x) : ℝ) : ℂ) := by
  rw [upperGammaComplement, Complex.GammaIntegral_one, partialGamma_one]
  push_cast
  ring

/-- Complementary incomplete Gamma at positive integer shape `k + 1`. -/
noncomputable def upperGammaNat (k : ℕ) (x : ℝ) : ℂ :=
  upperGammaComplement ((k + 1 : ℕ) : ℂ) x

/-- The complementary and lower incomplete Gamma integrals add to the complete Gamma integral. -/
theorem upperGammaNat_add_partialGamma (k : ℕ) (x : ℝ) :
    upperGammaNat k x + Complex.partialGamma ((k + 1 : ℕ) : ℂ) x =
      Complex.GammaIntegral ((k + 1 : ℕ) : ℂ) := by
  simp [upperGammaNat, upperGammaComplement]

/-- At threshold zero, the upper incomplete Gamma equals the complete Gamma integral. -/
theorem upperGammaNat_zero_eq_GammaIntegral (k : ℕ) :
    upperGammaNat k 0 = Complex.GammaIntegral ((k + 1 : ℕ) : ℂ) := by
  rw [upperGammaNat, upperGammaComplement]
  simp [Complex.partialGamma]

@[simp]
theorem upperGammaNat_zero (x : ℝ) : upperGammaNat 0 x = (-x).exp := by
  simpa [upperGammaNat] using upperGammaComplement_one x

/-- Integer-shape recurrence, the basis for the paper's finite-sum formula. -/
theorem upperGammaNat_succ (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    upperGammaNat (k + 1) x =
      ((k + 1 : ℕ) : ℂ) * upperGammaNat k x +
        (-x).exp * x ^ ((k + 1 : ℕ) : ℂ) := by
  have hs : 0 < (((k + 1 : ℕ) : ℂ).re) := by
    simp only [Nat.cast_add, Nat.cast_one]
    exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg k) zero_lt_one
  simpa [upperGammaNat, Nat.cast_add, Nat.cast_one] using
    (upperGammaComplement_add_one (s := ((k + 1 : ℕ) : ℂ)) hs hx)

/-- The elementary finite-sum expression for the complementary Gamma at integer shape. -/
noncomputable def upperGammaNatFinite (k : ℕ) (x : ℝ) : ℂ :=
  (Nat.factorial k : ℂ) * (-x).exp *
    ∑ j ∈ Finset.range (k + 1), (x : ℂ) ^ j / (Nat.factorial j : ℂ)

/-- Integer-shape upper incomplete Gamma is a finite exponential-polynomial sum. -/
theorem upperGammaNat_eq_finite (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    upperGammaNat k x = upperGammaNatFinite k x := by
  induction k with
  | zero =>
      simp [upperGammaNatFinite]
  | succ k ih =>
      rw [upperGammaNat_succ k hx, ih]
      simp only [upperGammaNatFinite, Nat.factorial_succ, Finset.sum_range_succ]
      have hfac : (Nat.factorial (k + 1) : ℂ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (k + 1)
      have hfac' : (Nat.factorial k : ℂ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero k
      have hpow : (x : ℂ) ^ ((k : ℂ) + 1) =
          (x : ℂ) * (x : ℂ) ^ k := by
        calc
          (x : ℂ) ^ ((k : ℂ) + 1) = (x : ℂ) ^ ((k + 1 : ℕ) : ℂ) := by
            congr 1
            simp only [Nat.cast_succ]
          _ = (x : ℂ) ^ (k + 1) := Complex.cpow_natCast _ _
          _ = (x : ℂ) * (x : ℂ) ^ k := by rw [pow_succ]; ring
      field_simp [hfac, hfac']
      push_cast
      rw [hpow]
      ring_nf

end JinWishart
