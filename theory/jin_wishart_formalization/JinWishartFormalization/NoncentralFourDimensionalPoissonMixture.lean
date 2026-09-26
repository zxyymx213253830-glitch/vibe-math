import JinWishartFormalization.NoncentralFourDimensionalRadial

/-!
# A Poisson mixture for the four-dimensional radial kernel

This pointwise identity is the analytic entry point for a proof of the
noncentral two-row, one-column Wishart law without an `S³` chart.  The
summands are the radial densities of central chi laws with `4 + 2n` real
degrees of freedom.  Identifying the actual shifted Gaussian law with this
mixture remains a separate probability argument.
-/

namespace JinWishart

noncomputable section

/-- The `n`th Poisson-weighted central radial density. -/
def chiFourPoissonTerm (a r : ℝ) (n : ℕ) : ℝ :=
  (Real.exp (-(a ^ 2 / 2)) * ((a ^ 2 / 2) ^ n / (n.factorial : ℝ))) *
    (r ^ (2 * n + 3) * Real.exp (-(r ^ 2 / 2)) /
      (2 ^ (n + 1) * ((n + 1).factorial : ℝ)))

/-- The candidate four-dimensional noncentral radial kernel is a Poisson
mixture of central radial kernels. -/
theorem noncentralChiFourRadialKernel_eq_poissonMixture
    (a r : ℝ) (ha : a ≠ 0) :
    noncentralChiFourRadialKernel a r =
      ∑' n : ℕ, chiFourPoissonTerm a r n := by
  unfold noncentralChiFourRadialKernel besselI1RealSeries chiFourPoissonTerm
  have hfactor (n : ℕ) :
      (r ^ 2 / a) * Real.exp (-((r ^ 2 + a ^ 2) / 2)) *
          ((a * r / 2) *
            (((a * r) ^ 2 / 4) ^ n /
              ((n.factorial : ℝ) * ((n + 1).factorial : ℝ)))) =
        (Real.exp (-(a ^ 2 / 2)) *
            ((a ^ 2 / 2) ^ n / (n.factorial : ℝ))) *
          (r ^ (2 * n + 3) * Real.exp (-(r ^ 2 / 2)) /
            (2 ^ (n + 1) * ((n + 1).factorial : ℝ))) := by
    rw [show -((r ^ 2 + a ^ 2) / 2) = -(a ^ 2 / 2) + -(r ^ 2 / 2) by ring,
      Real.exp_add]
    rw [show ((a * r) ^ 2 / 4) ^ n = (a ^ 2 / 2) ^ n * (r ^ 2 / 2) ^ n by
      rw [show (a * r) ^ 2 / 4 = (a ^ 2 / 2) * (r ^ 2 / 2) by ring, mul_pow]]
    rw [show (r ^ 2 / 2) ^ n = r ^ (2 * n) / 2 ^ n by
      rw [div_pow, ← pow_mul]]
    rw [show r ^ (2 * n + 3) = r ^ 2 * r ^ (2 * n) * r by
      rw [show 2 * n + 3 = 2 + 2 * n + 1 by omega, pow_add, pow_add, pow_one]]
    rw [pow_succ]
    have hn : (n.factorial : ℝ) ≠ 0 := by positivity
    have hn1 : ((n + 1).factorial : ℝ) ≠ 0 := by positivity
    have hpow : (2 : ℝ) ^ n ≠ 0 := by positivity
    field_simp [ha, hn, hn1, hpow]
    ring
  calc
    _ = (r ^ 2 / a) * Real.exp (-((r ^ 2 + a ^ 2) / 2)) *
        ((a * r / 2) * ∑' n : ℕ,
          ((a * r) ^ 2 / 4) ^ n /
            ((n.factorial : ℝ) * ((n + 1).factorial : ℝ))) := by rfl
    _ = ∑' n : ℕ,
          (r ^ 2 / a) * Real.exp (-((r ^ 2 + a ^ 2) / 2)) *
            ((a * r / 2) *
              (((a * r) ^ 2 / 4) ^ n /
                ((n.factorial : ℝ) * ((n + 1).factorial : ℝ)))) := by
      rw [← tsum_mul_left, ← tsum_mul_left]
    _ = _ := by
      apply tsum_congr
      intro n
      exact hfactor n

end

end JinWishart
