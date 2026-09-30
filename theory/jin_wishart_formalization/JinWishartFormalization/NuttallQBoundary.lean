import JinWishartFormalization.NuttallQ21Normalization
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Gaussian moments for the general Nuttall-Q boundary calculation

The zero-threshold identity for `Q_{t,t-1}` reduces, term by term in the
modified-Bessel series, to odd Gaussian moments.  This file records the
dimension-uniform moment identity used in that reduction.

`NuttallQ21Normalization.gaussianOddMoment` already covers the exponent `2n+3`
for every `n`, so the only new work is the `N = 0` base case
`∫₀^∞ r e^{-r²/2} dr = 1`, obtained from the Gamma integral
`∫₀^∞ x^q e^{-b x^p} dx = b^{-(q+1)/p} (1/p) Γ((q+1)/p)` at `p = 2`, `q = 1`,
`b = 1/2`.
-/

open MeasureTheory Set

namespace JinWishart

/-- Odd Gaussian moment, `N = 0` base case: `∫₀^∞ r e^{-r²/2} dr = 1`. -/
theorem gaussianOddMoment_zero :
    ∫ r in Ioi (0 : ℝ), r ^ (2 * 0 + 1) * Real.exp (-(r ^ 2 / 2)) =
      2 ^ 0 * ((0 : ℕ).factorial : ℝ) := by
  have hbase := integral_rpow_mul_exp_neg_mul_rpow (p := (2 : ℝ)) (q := (1 : ℝ))
    (b := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  have hfun : (fun r : ℝ => r ^ (2 * 0 + 1) * Real.exp (-(r ^ 2 / 2))) =
      fun r : ℝ => r ^ (1 : ℝ) * Real.exp (-(1 / 2 : ℝ) * r ^ (2 : ℝ)) := by
    funext r
    simp only [Nat.mul_zero, Nat.add_zero, pow_one, Real.rpow_one, Real.rpow_two]
    ring_nf
  rw [hfun, hbase]
  norm_num [Real.Gamma_one]

/-- The odd Gaussian moment with exponent `2*N+1`, in the normalization of
the Nuttall-Q kernel. -/
theorem gaussianOddMoment_general (N : ℕ) :
    ∫ r in Ioi (0 : ℝ), r ^ (2 * N + 1) * Real.exp (-(r ^ 2 / 2)) =
      2 ^ N * (N.factorial : ℝ) := by
  cases N with
  | zero => exact gaussianOddMoment_zero
  | succ M =>
      simpa [show 2 * (M + 1) + 1 = 2 * M + 3 by omega] using gaussianOddMoment M

/-- The moment arising from the `n`th Bessel-series term at Nuttall order
`(t,t-1)`. -/
theorem gaussianOddMoment_nuttall (t n : ℕ) :
    ∫ r in Ioi (0 : ℝ), r ^ (2 * (n + t - 1) + 1) *
        Real.exp (-(r ^ 2 / 2)) =
      2 ^ (n + t - 1) * ((n + t - 1).factorial : ℝ) :=
  gaussianOddMoment_general (n + t - 1)

end JinWishart
