import JinWishartFormalization.NuttallQ

/-!
# Series representation of the order-zero modified Bessel function

This module starts from the actual definition used in `NuttallQ.lean` and
connects it to Mathlib's regularized `₀F₁` series.  No integral or positivity
representation is assumed here.
-/

namespace JinWishart

/-- The order-zero modified Bessel function is the regularized `₀F₁(;1;z²/4)`.
This identifies the library special function before extracting its coefficient
series. -/
theorem modifiedBesselI_zero_eq_regularizedHG (z : ℂ) :
    modifiedBesselI 0 z = Complex.regularizedHGFun 0 {1} (z ^ 2 / 4) := by
  simp only [modifiedBesselI, pow_zero, one_mul, Complex.besselJ_def]
  norm_num
  congr 1
  simp only [div_eq_mul_inv, mul_pow, Complex.I_sq, inv_pow]
  field_simp
  ring

/-- The coefficient of the regularized `₀F₁(;1;z)` series is `1/(n!)²`. -/
theorem regularizedHGFunCoeff_zero_singleton_one (n : ℕ) :
    Complex.regularizedHGFunCoeff 0 {1} n =
      (((n.factorial : ℂ) ^ 2)⁻¹) := by
  simp [Complex.regularizedHGFunCoeff]
  rw [show (1 : ℂ) + (n : ℂ) = (n : ℂ) + 1 by ring,
    Complex.Gamma_nat_eq_factorial]
  field_simp

/-- The regularized hypergeometric function in the previous theorem is the
power series with the coefficients just computed. -/
theorem regularizedHGFun_zero_singleton_one_eq_tsum (z : ℂ) :
    Complex.regularizedHGFun 0 {1} z =
      ∑' n : ℕ, Complex.regularizedHGFunCoeff 0 {1} n * z ^ n := by
  rw [Complex.regularizedHGFun, Complex.regularizedHGFunSeries]
  change FormalMultilinearSeries.ofScalarsSum
    (Complex.regularizedHGFunCoeff 0 {1}) z = _
  rw [FormalMultilinearSeries.ofScalars_sum_eq]
  simp only [smul_eq_mul]

/-- The defining series of the order-zero modified Bessel function, with
factorial coefficients exposed. -/
theorem modifiedBesselI_zero_eq_factorialSeries (z : ℂ) :
    modifiedBesselI 0 z =
      ∑' n : ℕ, (z ^ 2 / 4) ^ n / ((n.factorial : ℂ) ^ 2) := by
  rw [modifiedBesselI_zero_eq_regularizedHG,
    regularizedHGFun_zero_singleton_one_eq_tsum]
  simp_rw [regularizedHGFunCoeff_zero_singleton_one]
  congr 1
  funext n
  ring

/-- For real input, the complex Bessel value is the complex embedding of a
real factorial series. -/
theorem modifiedBesselI_zero_ofReal_eq_realSeries (x : ℝ) :
    (((∑' n : ℕ, (x ^ 2 / 4) ^ n / ((n.factorial : ℝ) ^ 2)) : ℝ) : ℂ) =
      modifiedBesselI 0 (x : ℂ) := by
  rw [Complex.ofReal_tsum, modifiedBesselI_zero_eq_factorialSeries]
  apply tsum_congr
  intro n
  push_cast
  ring

/-- Every term in the real factorial series is nonnegative, hence its sum is
nonnegative. -/
theorem besselI0RealSeries_nonneg (x : ℝ) :
    0 ≤ ∑' n : ℕ, (x ^ 2 / 4) ^ n / ((n.factorial : ℝ) ^ 2) := by
  apply tsum_nonneg
  intro n
  positivity

/-- The order-zero modified Bessel value at a real input has zero imaginary part. -/
theorem modifiedBesselI_zero_ofReal_im (x : ℝ) :
    (modifiedBesselI 0 (x : ℂ)).im = 0 := by
  rw [← modifiedBesselI_zero_ofReal_eq_realSeries]
  simp

/-- The order-zero modified Bessel value at a real input is nonnegative. -/
theorem modifiedBesselI_zero_ofReal_re_nonneg (x : ℝ) :
    0 ≤ (modifiedBesselI 0 (x : ℂ)).re := by
  rw [← modifiedBesselI_zero_ofReal_eq_realSeries]
  simp only [Complex.ofReal_re]
  exact besselI0RealSeries_nonneg x

end JinWishart
