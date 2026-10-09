import JinWishartFormalization.GaussianTwoColumnIntegration

/-!
# Complex unitary frames in actual two-column Gaussian coordinates

Complex linear isometries preserve the complex inner product, unlike arbitrary
real rotations. The real/complex conversion is explicit, with no sqrt(2) in
the isometry; the actual complex sample has the additional variance factor.
[需人工审查] Coordinate convention and measurable frame hypotheses.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace JinWishart

noncomputable section

abbrev ComplexColumnSpace (m : ℕ) := EuclideanSpace ℂ (Fin m)

/-- The product of the existing `1,I` bases gives a real isometry to complex columns. -/
def complexColumnCoordinates (m : ℕ) : TwoColumnBlock m ≃ₗᵢ[ℝ] ComplexColumnSpace m :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.sigmaEquivProd (Fin m) (Fin 2)).symm).trans
    (Pi.orthonormalBasis (fun _ : Fin m => Complex.orthonormalBasisOneI)).repr.symm

theorem complexColumnCoordinates_apply {m : ℕ} (u : TwoColumnBlock m) (i : Fin m) :
    complexColumnCoordinates m u i = (u (i, 0) : ℂ) + u (i, 1) * Complex.I := by
  rfl

theorem complexColumnCoordinates_join_first {m : ℕ} (u v : TwoColumnBlock m) (i : Fin m) :
    complexSampleMatrix (twoColumnJoin (u, v)) i 0 =
      complexColumnCoordinates m u i / Real.sqrt 2 := by
  rw [twoColumnJoin_complex_first, complexColumnCoordinates_apply]
  congr 2
  ring

theorem complexColumnCoordinates_join_second {m : ℕ} (u v : TwoColumnBlock m) (i : Fin m) :
    complexSampleMatrix (twoColumnJoin (u, v)) i 1 =
      complexColumnCoordinates m v i / Real.sqrt 2 := by
  rw [twoColumnJoin_complex_second, complexColumnCoordinates_apply]
  congr 2
  ring

/-- Restrict a genuine complex unitary isometry to real scalars, keeping its norm. -/
def complexFrameToReal {m : ℕ} (U : ComplexColumnSpace m ≃ₗᵢ[ℂ] ComplexColumnSpace m) :
    ComplexColumnSpace m ≃ₗᵢ[ℝ] ComplexColumnSpace m where
  toLinearEquiv := U.toLinearEquiv.restrictScalars ℝ
  norm_map' := U.norm_map

/-- Express a complex unitary frame as an encoded real-coordinate isometry. -/
def encodedComplexFrame {m : ℕ} (U : ComplexColumnSpace m ≃ₗᵢ[ℂ] ComplexColumnSpace m) :
    TwoColumnBlock m ≃ₗᵢ[ℝ] TwoColumnBlock m :=
  (complexColumnCoordinates m).trans
    ((complexFrameToReal U).trans (complexColumnCoordinates m).symm)

theorem complexColumnCoordinates_encodedFrame {m : ℕ}
    (U : ComplexColumnSpace m ≃ₗᵢ[ℂ] ComplexColumnSpace m) (u : TwoColumnBlock m) :
    complexColumnCoordinates m (encodedComplexFrame U u) = U (complexColumnCoordinates m u) := by
  simp only [encodedComplexFrame, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply]
  rfl

/-- The Gram off-diagonal inner product is preserved by a genuine complex frame. -/
theorem complexFrame_inner_preserved {m : ℕ}
    (U : ComplexColumnSpace m ≃ₗᵢ[ℂ] ComplexColumnSpace m) (u v : TwoColumnBlock m) :
    inner ℂ (complexColumnCoordinates m (encodedComplexFrame U u))
      (complexColumnCoordinates m (encodedComplexFrame U v)) =
    inner ℂ (complexColumnCoordinates m u) (complexColumnCoordinates m v) := by
  rw [complexColumnCoordinates_encodedFrame, complexColumnCoordinates_encodedFrame]
  exact U.inner_map_map _ _

/-- The actual encoded Gaussian column is invariant under a fixed complex frame. -/
theorem encodedComplexFrame_gaussianLaw {m : ℕ}
    (U : ComplexColumnSpace m ≃ₗᵢ[ℂ] ComplexColumnSpace m) :
    (stdGaussian (TwoColumnBlock m)).map (encodedComplexFrame U) =
      stdGaussian (TwoColumnBlock m) := stdGaussian_map _

/-- Preserve the second-column Gaussian law in a measurable complex unitary
frame selected from the first column, on the actual matrix sample. -/
theorem twoColumn_complex_fiber_frame_law (m : ℕ)
    (U : ComplexColumnSpace m → ComplexColumnSpace m ≃ₗᵢ[ℂ] ComplexColumnSpace m)
    (hU : Measurable (fun p : ComplexColumnSpace m × ComplexColumnSpace m => U p.1 p.2)) :
    (stdGaussian (ComplexSample (m := m) (n := 2))).map
      (fun z => ((twoColumnSplit z).1,
        encodedComplexFrame (U (complexColumnCoordinates m (twoColumnSplit z).1))
          (twoColumnSplit z).2)) =
      (stdGaussian (TwoColumnBlock m)).prod (stdGaussian (TwoColumnBlock m)) := by
  apply twoColumn_rotated_split_law m
    (fun u => encodedComplexFrame (U (complexColumnCoordinates m u)))
  change Measurable (fun p : TwoColumnBlock m × TwoColumnBlock m =>
    (complexColumnCoordinates m).symm (U (complexColumnCoordinates m p.1)
      (complexColumnCoordinates m p.2)))
  exact (complexColumnCoordinates m).symm.continuous.measurable.comp
    (hU.comp ((complexColumnCoordinates m).continuous.measurable.prodMap
      (complexColumnCoordinates m).continuous.measurable))

def complexColumnPair {m : ℕ} (a b : ComplexColumnSpace m) : Matrix (Fin m) (Fin 2) ℂ :=
  fun i j => if j = 0 then a i else b i

theorem complexColumnPair_gram_entry {m : ℕ} (a b : ComplexColumnSpace m) (i j : Fin 2) :
    complexGram (complexColumnPair a b) i j =
      inner ℂ (if i = 0 then a else b) (if j = 0 then a else b) := by
  simp only [complexGram, Matrix.mul_apply, Matrix.conjTranspose_apply,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
    simp [complexColumnPair, hi, hj, mul_comm]

/-- A common complex unitary frame preserves the full two-column Gram matrix. -/
theorem complexColumnPair_gram_unitary {m : ℕ}
    (U : ComplexColumnSpace m ≃ₗᵢ[ℂ] ComplexColumnSpace m) (a b : ComplexColumnSpace m) :
    complexGram (complexColumnPair (U a) (U b)) = complexGram (complexColumnPair a b) := by
  ext i j
  rw [complexColumnPair_gram_entry, complexColumnPair_gram_entry]
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;>
    simp only [hi, hj, ite_true, ite_false] <;> exact U.inner_map_map _ _

/-- Actual circular variance-one complex column, including the sqrt(2) scaling. -/
def actualComplexColumn {m : ℕ} (u : TwoColumnBlock m) : ComplexColumnSpace m :=
  (Real.sqrt 2)⁻¹ • complexColumnCoordinates m u

theorem actualComplexColumn_encodedFrame {m : ℕ}
    (U : ComplexColumnSpace m ≃ₗᵢ[ℂ] ComplexColumnSpace m) (u : TwoColumnBlock m) :
    actualComplexColumn (encodedComplexFrame U u) = U (actualComplexColumn u) := by
  unfold actualComplexColumn
  rw [complexColumnCoordinates_encodedFrame]
  exact ((complexFrameToReal U).map_smul (Real.sqrt 2)⁻¹ (complexColumnCoordinates m u)).symm

theorem twoColumnJoin_matrix_eq_columnPair {m : ℕ} (u v : TwoColumnBlock m) :
    complexSampleMatrix (twoColumnJoin (u, v)) =
      complexColumnPair (actualComplexColumn u) (actualComplexColumn v) := by
  ext i j
  fin_cases j <;>
    simp [complexColumnPair, actualComplexColumn, complexColumnCoordinates_join_first,
      complexColumnCoordinates_join_second, inv_mul_eq_div, Complex.real_smul]

/-- Deterministic actual-model Gram invariance. This is not a distributional
claim that the aligned first column remains Gaussian. -/
theorem twoColumn_actualGram_unitary {m : ℕ}
    (U : ComplexColumnSpace m ≃ₗᵢ[ℂ] ComplexColumnSpace m) (u v : TwoColumnBlock m) :
    complexGram (complexSampleMatrix
      (twoColumnJoin (encodedComplexFrame U u, encodedComplexFrame U v))) =
      complexGram (complexSampleMatrix (twoColumnJoin (u, v))) := by
  rw [twoColumnJoin_matrix_eq_columnPair, twoColumnJoin_matrix_eq_columnPair,
    actualComplexColumn_encodedFrame, actualComplexColumn_encodedFrame]
  exact complexColumnPair_gram_unitary U _ _

end

end JinWishart
