import JinWishartFormalization.ThreeRowSampleCoordinates

/-!
# Norm of the encoded three-row complex mean

The Gaussian sample space stores each complex entry as two real coordinates,
scaled by `sqrt 2`. This file records the resulting exact conversion between
the encoded Euclidean norm and the Frobenius energy of a `3 × 1` mean matrix.
-/

namespace JinWishart

noncomputable section

/-- The real-coordinate encoding of a complex `3 × 1` mean has squared norm
twice the complex Frobenius energy. -/
theorem threeRowComplexSampleMean_norm_sq_div_two
    (M : Matrix (Fin 3) (Fin 1) ℂ) :
    ‖complexSampleMean M‖ ^ 2 / 2 =
      ∑ i : Fin 3, ‖M i 0‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [complexSampleMean, Fintype.sum_prod_type, Fin.sum_univ_three]
  simp only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [Complex.sq_norm, Complex.normSq_apply,
    Complex.sq_norm, Complex.normSq_apply,
    Complex.sq_norm, Complex.normSq_apply]
  ring

/-- In the `Fin 6` coordinates actually used by the radial model, the
noncentrality parameter `lambda` is exactly the sum of squared magnitudes of
the three complex mean entries. -/
theorem threeRowSampleToFin6_mean_norm_sq_eq_twice_frobenius
    (M : Matrix (Fin 3) (Fin 1) ℂ) :
    ‖threeRowSampleToFin6 (complexSampleMean M)‖ ^ 2 =
      2 * ∑ i : Fin 3, ‖M i 0‖ ^ 2 := by
  rw [threeRowSampleToFin6.norm_map]
  have h := threeRowComplexSampleMean_norm_sq_div_two M
  nlinarith

end

end JinWishart
