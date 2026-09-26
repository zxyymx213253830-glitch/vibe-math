import JinWishartFormalization.BesselI1Series

/-!
# Four-real-dimensional noncentral Gaussian radial kernel

For a noncentral standard Gaussian in four real dimensions, the spherical
average contributes `I₁(ar)/(ar)`.  After multiplying by the radius-cubed
Jacobian, the radial density is `r²/a` times the Nuttall `(2,1)` kernel.
This module proves the local kernel identity; the geometric polar-coordinate
integral and probability pushforward remain separate obligations.
-/

namespace JinWishart

noncomputable section

/-- Real factorial-series value of the order-one modified Bessel function. -/
def besselI1RealSeries (x : ℝ) : ℝ :=
  (x / 2) * ∑' n : ℕ,
    (x ^ 2 / 4) ^ n / ((n.factorial : ℝ) * ((n + 1).factorial : ℝ))

/-- Four-dimensional noncentral Gaussian radial density kernel, in the radius
coordinate and with noncentrality amplitude `a > 0`. -/
def noncentralChiFourRadialKernel (a r : ℝ) : ℝ :=
  (r ^ 2 / a) * Real.exp (-((r ^ 2 + a ^ 2) / 2)) * besselI1RealSeries (a * r)

/-- The order-one real series is nonnegative at nonnegative arguments. -/
theorem besselI1RealSeries_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ besselI1RealSeries x := by
  unfold besselI1RealSeries
  apply mul_nonneg (div_nonneg hx (by norm_num))
  apply tsum_nonneg
  intro n
  positivity

/-- The four-dimensional radial kernel is nonnegative for positive
noncentrality and nonnegative radius. -/
theorem noncentralChiFourRadialKernel_nonneg {a r : ℝ}
    (ha : 0 < a) (hr : 0 ≤ r) :
    0 ≤ noncentralChiFourRadialKernel a r := by
  unfold noncentralChiFourRadialKernel
  apply mul_nonneg
  · apply mul_nonneg
    · exact div_nonneg (sq_nonneg r) ha.le
    · exact Real.exp_nonneg _
  · exact besselI1RealSeries_nonneg (mul_nonneg ha.le hr)

/-- The four-dimensional radial density kernel equals the `(p,q)=(2,1)`
Nuttall-Q integrand divided by the noncentrality amplitude.  The division by
`a` is exactly the `1/(a r)` factor from the normalized spherical integral,
combined with the `r^3` polar Jacobian. -/
theorem noncentralChiFourRadialKernel_eq_nuttallQ21_div
    (a r : ℝ) (_ha : a ≠ 0) :
    (noncentralChiFourRadialKernel a r : ℂ) =
      nuttallQIntegrand 2 1 a r / (a : ℂ) := by
  unfold noncentralChiFourRadialKernel besselI1RealSeries nuttallQIntegrand
  rw [← modifiedBesselI_one_ofReal_eq_realSeries (a * r)]
  push_cast
  field_simp

end

end JinWishart
