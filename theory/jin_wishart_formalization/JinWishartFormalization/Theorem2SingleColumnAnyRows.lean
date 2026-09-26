import JinWishartFormalization.Theorem1SingleColumnAnyRows

/-!
# Theorem 2 formula in the one-column full-rank case

For `s=L=1` and any positive row count `t`, the largest and smallest
eigenvalues coincide.  This module simplifies the Theorem 2 determinant
candidate to one normalized Nuttall-Q increment.  Equality with the actual
noncentral Wishart CDF beyond `t=1` is a separate analytic obligation.
-/

namespace JinWishart

/-- The one-column Theorem 2 formula is a normalized Nuttall-Q increment.
The denominator's nonvanishing is retained as an explicit hypothesis. -/
theorem theorem2OneColumnCandidate_eq_normalizedNuttallQIncrement
    (t : ℕ) (ht : 1 ≤ t) (lambda x : ℝ)
    (hden : nuttallQ t (t - 1) (Real.sqrt (2 * lambda)) 0 ≠ 0) :
    theorem2CdfCandidate 1 t 1 ht (by omega) (fun _ : Fin 1 => lambda) x =
      ‖nuttallQ t (t - 1) (Real.sqrt (2 * lambda)) 0 -
        nuttallQ t (t - 1) (Real.sqrt (2 * lambda))
          (Real.sqrt (2 * x))‖ /
        ‖nuttallQ t (t - 1) (Real.sqrt (2 * lambda)) 0‖ := by
  have hscale : theorem1FullRankRowScale 1 t (0 : Fin 1) ≠ 0 :=
    theorem1FullRankRowScale_ne_zero 1 t 0
  simp only [theorem2CdfCandidate, Matrix.det_fin_one]
  simp only [theorem2XiMatrix, theorem2XiEntry,
    theorem1PsiMatrix, theorem1PsiEntry]
  simp [theorem1QOrder] at *
  have horder : 1 + t - 2 + 1 = t := by omega
  rw [horder]
  have hfac : |(2 : ℝ) ^ ((2 - 1 - (t : ℝ)) / 2)| ≠ 0 := by positivity
  field_simp [hfac, norm_ne_zero_iff.mpr hden]

end JinWishart
