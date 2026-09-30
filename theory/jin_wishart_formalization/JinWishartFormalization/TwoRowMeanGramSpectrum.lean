import JinWishartFormalization.TwoRowSampleCoordinates

/-!
# Spectral meaning of the `2 × 1` noncentrality parameter

For any two-row, one-column mean, its Gram matrix is a `1 × 1`
positive-semidefinite matrix.  Its sole eigenvalue is the squared Frobenius
norm of the mean, which is also half the squared norm of its real Gaussian
coordinate encoding.
-/

open MeasureTheory ProbabilityTheory

namespace JinWishart

noncomputable section

/-- The unique eigenvalue of the `1 × 1` Gram matrix `Mᴴ M` is its trace,
namely the squared Frobenius norm of the complex mean matrix. -/
theorem twoRowMeanGram_uniqueEigenvalue_eq_frobeniusSq
    (M : Matrix (Fin 2) (Fin 1) ℂ) :
    (complexGram_posSemidef M).1.eigenvalues₀
        (smallestEigenvalue₀Index (n := 1) (by norm_num)) =
      ∑ i : Fin 2, ‖M i 0‖ ^ 2 := by
  have hsample : complexSampleMatrix (complexSampleMean M) = M := by
    have hz : complexSampleMatrix (0 : ComplexSample (m := 2) (n := 1)) = 0 := by
      ext i j
      simp [complexSampleMatrix]
    have h := complexSampleMatrix_add_mean
      (x := (0 : ComplexSample (m := 2) (n := 1))) M
    rw [hz] at h
    simpa using h
  have henergy :
      complexNoncentralSampleSmallestEigenvalue
          (0 : Matrix (Fin 2) (Fin 1) ℂ) (by norm_num)
          (complexSampleMean M) =
        centralColumnSampleEnergy (complexSampleMean M) :=
    centralColumnSampleSmallestEigenvalue_eq_energy
      (m := 2) (by norm_num) (complexSampleMean M)
  have hspec :
      (complexGram_posSemidef M).1.eigenvalues₀
          (smallestEigenvalue₀Index (n := 1) (by norm_num)) =
        centralColumnSampleEnergy (complexSampleMean M) := by
    simpa [complexNoncentralSampleSmallestEigenvalue, complexGram, hsample] using henergy
  rw [hspec, centralColumnSampleEnergy_eq_euclideanEnergy,
    twoRowComplexMean_norm_sq_div_two]

/-- The same sole Gram eigenvalue is `‖complexSampleMean M‖² / 2` in the
real-coordinate Gaussian representation. -/
theorem twoRowMeanGram_uniqueEigenvalue_eq_realCoordinateEnergy
    (M : Matrix (Fin 2) (Fin 1) ℂ) :
    (complexGram_posSemidef M).1.eigenvalues₀
        (smallestEigenvalue₀Index (n := 1) (by norm_num)) =
      ‖complexSampleMean M‖ ^ 2 / 2 := by
  rw [twoRowMeanGram_uniqueEigenvalue_eq_frobeniusSq,
    ← twoRowComplexMean_norm_sq_div_two]

end

end JinWishart
