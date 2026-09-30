import JinWishartFormalization.NoncentralSixDimensionalRadial
import JinWishartFormalization.NoncentralFourDimensionalRadial

/-!
# Even-dimensional noncentral chi kernels as Poisson mixtures

For every `k : ℕ`, the noncentral radial kernel in real dimension
`2 * (k + 1)` is a Poisson mixture of central radial kernels whose degrees
of freedom are `2 * (k + n + 1)`.  This is an exact pointwise power-series
identity.  It is an analytic bridge toward general-row, one-column Wishart
CDFs; it does not identify the mixture with a shifted Gaussian probability
law or prove the paper's Nuttall-Q determinant formula.
-/

namespace JinWishart

noncomputable section

/-- Factorial-series radial kernel for a noncentral standard Gaussian in
`2 * (k + 1)` real dimensions. -/
def noncentralChiEvenRadialKernel (k : ℕ) (a r : ℝ) : ℝ :=
  (r ^ (2 * k + 1) / 2 ^ k) *
    Real.exp (-((r ^ 2 + a ^ 2) / 2)) *
      ∑' n : ℕ,
        ((a * r) ^ 2 / 4) ^ n /
          ((n.factorial : ℝ) * ((n + k).factorial : ℝ))

/-- The `n`th Poisson-weighted central radial density in dimension
`2 * (k + n + 1)`. -/
def chiEvenPoissonTerm (k : ℕ) (a r : ℝ) (n : ℕ) : ℝ :=
  (Real.exp (-(a ^ 2 / 2)) *
      ((a ^ 2 / 2) ^ n / (n.factorial : ℝ))) *
    (r ^ (2 * n + 2 * k + 1) * Real.exp (-(r ^ 2 / 2)) /
      (2 ^ (n + k) * ((n + k).factorial : ℝ)))

/-- In every even real dimension at least two, the noncentral radial
factorial series is exactly the Poisson mixture of central chi radial
kernels. -/
theorem noncentralChiEvenRadialKernel_eq_poissonMixture
    (k : ℕ) (a r : ℝ) :
    noncentralChiEvenRadialKernel k a r =
      ∑' n : ℕ, chiEvenPoissonTerm k a r n := by
  unfold noncentralChiEvenRadialKernel chiEvenPoissonTerm
  have hfactor (n : ℕ) :
      (r ^ (2 * k + 1) / 2 ^ k) *
          Real.exp (-((r ^ 2 + a ^ 2) / 2)) *
          (((a * r) ^ 2 / 4) ^ n /
            ((n.factorial : ℝ) * ((n + k).factorial : ℝ))) =
        (Real.exp (-(a ^ 2 / 2)) *
            ((a ^ 2 / 2) ^ n / (n.factorial : ℝ))) *
          (r ^ (2 * n + 2 * k + 1) * Real.exp (-(r ^ 2 / 2)) /
            (2 ^ (n + k) * ((n + k).factorial : ℝ))) := by
    rw [show -((r ^ 2 + a ^ 2) / 2) =
        -(a ^ 2 / 2) + -(r ^ 2 / 2) by ring, Real.exp_add]
    rw [show ((a * r) ^ 2 / 4) ^ n =
        (a ^ 2 / 2) ^ n * (r ^ 2 / 2) ^ n by
          rw [show (a * r) ^ 2 / 4 = (a ^ 2 / 2) * (r ^ 2 / 2) by ring,
            mul_pow]]
    rw [show (r ^ 2 / 2) ^ n = r ^ (2 * n) / 2 ^ n by
      rw [div_pow, ← pow_mul]]
    rw [show (2 : ℝ) ^ (n + k) = 2 ^ k * 2 ^ n by
      rw [Nat.add_comm n k, pow_add]]
    have hn : (n.factorial : ℝ) ≠ 0 := by positivity
    have hnk : ((n + k).factorial : ℝ) ≠ 0 := by positivity
    have hpow : (2 : ℝ) ^ n ≠ 0 := by positivity
    have hpowk : (2 : ℝ) ^ k ≠ 0 := by positivity
    have hpowR : r ^ (2 * k + 1) * r ^ (2 * n) =
        r ^ (2 * n + 2 * k + 1) := by
      rw [← pow_add]
      congr 1
      omega
    field_simp [hn, hnk, hpow, hpowk]
    calc
      _ = (a ^ 2 / 2) ^ n *
          (r ^ (2 * k + 1) * r ^ (2 * n)) := by ring
      _ = (a ^ 2 / 2) ^ n * r ^ (2 * n + 2 * k + 1) := by
        rw [hpowR]
      _ = _ := by ring
  calc
    _ = ((r ^ (2 * k + 1) / 2 ^ k) *
        Real.exp (-((r ^ 2 + a ^ 2) / 2))) *
        ∑' n : ℕ,
          (((a * r) ^ 2 / 4) ^ n /
            ((n.factorial : ℝ) * ((n + k).factorial : ℝ))) := by ring
    _ = ((r ^ (2 * k + 1) / 2 ^ k) *
        (Real.exp (-((r ^ 2 + a ^ 2) / 2)) *
          ∑' n : ℕ,
            (((a * r) ^ 2 / 4) ^ n /
              ((n.factorial : ℝ) * ((n + k).factorial : ℝ))))) := by ring
    _ = ((r ^ (2 * k + 1) / 2 ^ k) *
        ∑' n : ℕ,
          Real.exp (-((r ^ 2 + a ^ 2) / 2)) *
            (((a * r) ^ 2 / 4) ^ n /
              ((n.factorial : ℝ) * ((n + k).factorial : ℝ)))) := by
      rw [← tsum_mul_left]
    _ = ∑' n : ℕ,
        (r ^ (2 * k + 1) / 2 ^ k) *
          (Real.exp (-((r ^ 2 + a ^ 2) / 2)) *
            (((a * r) ^ 2 / 4) ^ n /
              ((n.factorial : ℝ) * ((n + k).factorial : ℝ)))) := by
      rw [← tsum_mul_left]
    _ = ∑' n : ℕ,
        ((r ^ (2 * k + 1) / 2 ^ k) *
          Real.exp (-((r ^ 2 + a ^ 2) / 2))) *
          (((a * r) ^ 2 / 4) ^ n /
            ((n.factorial : ℝ) * ((n + k).factorial : ℝ))) := by
      apply tsum_congr
      intro n
      ring
    _ = _ := by
      apply tsum_congr
      intro n
      exact hfactor n

/-- The generalized kernel specializes exactly to the existing four-real-
dimensional kernel (`k = 1`). -/
theorem noncentralChiEvenRadialKernel_two_eq_four
    (a r : ℝ) (ha : a ≠ 0) :
    noncentralChiEvenRadialKernel 1 a r =
      noncentralChiFourRadialKernel a r := by
  unfold noncentralChiEvenRadialKernel noncentralChiFourRadialKernel
    besselI1RealSeries
  norm_num
  field_simp [ha]
  <;> ring_nf

/-- The generalized kernel specializes definitionally to the existing
six-real-dimensional radial-series kernel (`k = 2`). -/
theorem noncentralChiEvenRadialKernel_three_eq_six
    (a r : ℝ) :
    noncentralChiEvenRadialKernel 2 a r =
      noncentralChiSixRadialSeriesKernel a r := by
  norm_num [noncentralChiEvenRadialKernel,
    noncentralChiSixRadialSeriesKernel]

end

end JinWishart
