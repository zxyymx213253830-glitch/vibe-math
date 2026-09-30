import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Basic.Real.Basic

/-!
# Repeated roots of real monic quadratics

This is a small algebraic bridge only: it does not involve a Gram matrix, a measure, or a Wishart
distribution.
-/

namespace JinWishart

open Polynomial

/-- The monic quadratic `X² + bX + c`. -/
noncomputable def realQuadratic (b c : ℝ) : Polynomial ℝ :=
  X ^ 2 + C b * X + C c

@[simp]
theorem eval_realQuadratic (b c r : ℝ) :
    (realQuadratic b c).eval r = r ^ 2 + b * r + c := by
  simp [realQuadratic]

@[simp]
theorem eval_derivative_realQuadratic (b c r : ℝ) :
    (derivative (realQuadratic b c)).eval r = 2 * r + b := by
  simp only [realQuadratic, derivative_add, derivative_X_sq, derivative_C_mul_X,
    derivative_C, eval_add, eval_mul, eval_C, eval_X, eval_zero]
  ring

/-- A real root is repeated when its root multiplicity is strictly greater than one. -/
def HasRepeatedRealRoot (p : Polynomial ℝ) : Prop :=
  ∃ r : ℝ, 1 < p.rootMultiplicity r

/-- `X² + bX + c` has a repeated real root iff its quadratic discriminant vanishes. -/
theorem realQuadratic_hasRepeatedRealRoot_iff_discriminant_eq_zero (b c : ℝ) :
    HasRepeatedRealRoot (realQuadratic b c) ↔ b ^ 2 - 4 * c = 0 := by
  have hp : realQuadratic b c ≠ 0 := by
    intro hzero
    have hcoeff := congrArg (fun q : Polynomial ℝ => q.coeff 2) hzero
    have hlead : (realQuadratic b c).coeff 2 = 1 := by
      simp [realQuadratic]
    simp [hlead] at hcoeff
  constructor
  · rintro ⟨r, hr⟩
    have hroots := (Polynomial.one_lt_rootMultiplicity_iff_isRoot hp).mp hr
    rcases hroots with ⟨hroot, hderivative⟩
    have hroot' : r ^ 2 + b * r + c = 0 := by
      simpa only [Polynomial.IsRoot, eval_realQuadratic] using hroot
    have hderivative' : 2 * r + b = 0 := by
      simpa only [Polynomial.IsRoot, eval_derivative_realQuadratic] using hderivative
    nlinarith
  · intro hdisc
    let r : ℝ := -b / 2
    have hroot' : r ^ 2 + b * r + c = 0 := by
      dsimp [r]
      nlinarith
    have hderivative' : 2 * r + b = 0 := by
      dsimp [r]
      ring
    have hroot : (realQuadratic b c).IsRoot r := by
      simpa only [Polynomial.IsRoot, eval_realQuadratic] using hroot'
    have hderivative : (derivative (realQuadratic b c)).IsRoot r := by
      simpa only [Polynomial.IsRoot, eval_derivative_realQuadratic] using hderivative'
    have hr := (Polynomial.one_lt_rootMultiplicity_iff_isRoot hp).mpr ⟨hroot, hderivative⟩
    exact ⟨r, hr⟩

end JinWishart
