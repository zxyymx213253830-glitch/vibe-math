import JinWishartFormalization.NuttallQ

/-!
# Real factorial series for the order-one modified Bessel function

This is the first analytic bridge needed for the two-dimensional noncentral
complex Gaussian norm: its angular average is `I₀`, while the radial Jacobian
introduces `I₁` in the resulting noncentral chi-square density.
-/

namespace JinWishart

/-- The order-one modified Bessel function is a regularized `₀F₁` with
parameter `2`. -/
theorem modifiedBesselI_one_eq_regularizedHG (z : ℂ) :
    modifiedBesselI 1 z = (z / 2) * Complex.regularizedHGFun 0 {2} (z ^ 2 / 4) := by
  simp only [modifiedBesselI, Complex.besselJ_def]
  norm_num
  simp only [div_eq_mul_inv, mul_pow, Complex.I_sq, inv_pow]
  field_simp
  simp [Complex.I_sq]
  norm_num

/-- The regularized hypergeometric coefficient for parameter `2` is
`1 / (n! (n+1)!)`. -/
theorem regularizedHGFunCoeff_zero_singleton_two (n : ℕ) :
    Complex.regularizedHGFunCoeff 0 {2} n =
      (((n.factorial : ℂ) * ((n + 1).factorial : ℂ))⁻¹) := by
  simp only [Complex.regularizedHGFunCoeff, Multiset.map_zero, Multiset.prod_zero,
    Multiset.map_singleton, Multiset.prod_singleton]
  have harg : (2 : ℂ) + (n : ℂ) = ((n + 1 : ℕ) : ℂ) + 1 := by
    push_cast
    ring
  rw [harg, Complex.Gamma_nat_eq_factorial]
  push_cast
  simp only [Nat.factorial]
  field_simp

/-- The regularized hypergeometric function with parameter `2` is the
corresponding scalar power series. -/
theorem regularizedHGFun_zero_singleton_two_eq_tsum (z : ℂ) :
    Complex.regularizedHGFun 0 {2} z =
      ∑' n : ℕ, Complex.regularizedHGFunCoeff 0 {2} n * z ^ n := by
  rw [Complex.regularizedHGFun, Complex.regularizedHGFunSeries]
  change FormalMultilinearSeries.ofScalarsSum
    (Complex.regularizedHGFunCoeff 0 {2}) z = _
  rw [FormalMultilinearSeries.ofScalars_sum_eq]
  simp only [smul_eq_mul]

/-- Factorial-series expansion of the order-one modified Bessel function. -/
theorem modifiedBesselI_one_eq_factorialSeries (z : ℂ) :
    modifiedBesselI 1 z =
      (z / 2) * ∑' n : ℕ,
        (z ^ 2 / 4) ^ n /
          (((n.factorial : ℂ) * ((n + 1).factorial : ℂ))) := by
  rw [modifiedBesselI_one_eq_regularizedHG,
    regularizedHGFun_zero_singleton_two_eq_tsum]
  congr 1
  apply tsum_congr
  intro n
  rw [regularizedHGFunCoeff_zero_singleton_two]
  push_cast
  ring

/-- For real input, `I₁` is the complex embedding of the real factorial
series, including its leading `x/2` factor. -/
theorem modifiedBesselI_one_ofReal_eq_realSeries (x : ℝ) :
    (((x / 2) * ∑' n : ℕ,
        (x ^ 2 / 4) ^ n /
          ((n.factorial : ℝ) * ((n + 1).factorial : ℝ)) : ℝ) : ℂ) =
      modifiedBesselI 1 (x : ℂ) := by
  rw [Complex.ofReal_mul, Complex.ofReal_tsum,
    modifiedBesselI_one_eq_factorialSeries]
  have hhalf : ((x / 2 : ℝ) : ℂ) = (x : ℂ) / 2 := by push_cast; ring
  rw [hhalf]
  apply congrArg (fun z : ℂ => (x : ℂ) / 2 * z)
  apply tsum_congr
  intro n
  push_cast
  ring

end JinWishart
