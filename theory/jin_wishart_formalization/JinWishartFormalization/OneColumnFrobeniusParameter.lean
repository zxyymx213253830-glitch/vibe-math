import JinWishartFormalization.WishartProbability

/-!
# Arbitrary-row Frobenius noncentrality for a one-column Wishart sample

The real Gaussian encoding stores the real and imaginary parts of every
complex mean entry with a `sqrt 2` factor.  This module records the exact
parameter conversion uniformly in the number of rows, rather than proving
separate two- and three-row instances.
-/

namespace JinWishart

noncomputable section

/-- For every row dimension, the squared norm of the encoded one-column
complex mean is twice its complex Frobenius energy. -/
theorem complexSampleMean_oneColumn_norm_sq_div_two
    {m : ℕ} (M : Matrix (Fin m) (Fin 1) ℂ) :
    ‖complexSampleMean M‖ ^ 2 / 2 = ∑ i : Fin m, ‖M i 0‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [complexSampleMean, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring_nf

/-- The same statement, scaled to match the real-coordinate energy convention
used by the Gaussian radial model. -/
theorem complexSampleMean_oneColumn_norm_sq_eq_twice_frobenius
    {m : ℕ} (M : Matrix (Fin m) (Fin 1) ℂ) :
    ‖complexSampleMean M‖ ^ 2 = 2 * ∑ i : Fin m, ‖M i 0‖ ^ 2 := by
  have h := complexSampleMean_oneColumn_norm_sq_div_two M
  nlinarith

end

end JinWishart
