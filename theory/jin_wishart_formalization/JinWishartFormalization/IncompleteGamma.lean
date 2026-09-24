import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Incomplete Gamma recurrence used by the Wishart eigenvalue formulas

Mathlib provides the complete Gamma integral and the lower incomplete Gamma
integral together with integration-by-parts recurrences.  The upper incomplete
Gamma is introduced here as their algebraic complement.  Identifying this
complement with the improper tail integral on `(x, ∞)` is a separate measure-
theoretic lemma and is not claimed in this file yet.
-/

namespace JinWishart

/-- Algebraic complement of the lower incomplete Gamma integral. -/
noncomputable def upperGammaComplement (s : ℂ) (x : ℝ) : ℂ :=
  Complex.GammaIntegral s - Complex.partialGamma s x

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

end JinWishart
