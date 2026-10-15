import JinWishartFormalization.CentralWishartCone

/-!
# Real coordinates for Hermitian matrices in every dimension

The domain is `Matrix (Fin n) (Fin n) ℝ`: exactly n^2 real coordinates.
The upper triangle stores real parts; its transpose stores imaginary parts;
the diagonal is real. This avoids using 2n^2-dimensional complex-matrix
Lebesgue measure on a zero-volume Hermitian subset.

No Gaussian-to-Wishart density or volume normalization is asserted here.
[需人工审查] The eventual coordinate-volume normalization in the matrix law.
-/

open Matrix MeasureTheory
namespace JinWishart
noncomputable section

def hermitianOfRealCoordinates {n : ℕ} (q : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℂ := fun i j =>
  if i = j then (q i i : ℂ)
  else if i < j then (q i j : ℂ) + Complex.I * (q j i : ℂ)
  else (q j i : ℂ) - Complex.I * (q i j : ℂ)

def realCoordinatesOfHermitian {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j =>
  if i ≤ j then (A i j).re else -(A i j).im

theorem hermitianOfRealCoordinates_isHermitian {n : ℕ}
    (q : Matrix (Fin n) (Fin n) ℝ) : (hermitianOfRealCoordinates q).IsHermitian := by
  ext i j
  by_cases he : i = j
  · subst j
    simp [Matrix.conjTranspose_apply, hermitianOfRealCoordinates]
  · by_cases hl : i < j
    · have hj : ¬ j < i := not_lt_of_ge hl.le
      simp [Matrix.conjTranspose_apply, hermitianOfRealCoordinates, he, Ne.symm he,
        hl, hj, map_sub, map_add, map_mul, sub_eq_add_neg]
    · have hj : j < i := lt_of_le_of_ne (le_of_not_gt hl) (Ne.symm he)
      simp [Matrix.conjTranspose_apply, hermitianOfRealCoordinates, he, Ne.symm he,
        hl, hj, map_sub, map_add, map_mul, sub_eq_add_neg]

theorem realCoordinates_hermitianOfRealCoordinates {n : ℕ}
    (q : Matrix (Fin n) (Fin n) ℝ) :
    realCoordinatesOfHermitian (hermitianOfRealCoordinates q) = q := by
  ext i j
  by_cases he : i = j
  · subst j
    simp [realCoordinatesOfHermitian, hermitianOfRealCoordinates]
  · by_cases hl : i < j
    · simp [realCoordinatesOfHermitian, hermitianOfRealCoordinates, he, hl, hl.le]
    · have hj : j < i := lt_of_le_of_ne (le_of_not_gt hl) (Ne.symm he)
      simp [realCoordinatesOfHermitian, hermitianOfRealCoordinates, he, hl,
        not_le_of_gt hj]

theorem hermitianOfRealCoordinates_realCoordinates {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    hermitianOfRealCoordinates (realCoordinatesOfHermitian A) = A := by
  ext i j
  by_cases he : i = j
  · subst j
    have hi := congrArg Complex.im (hA.apply i i)
    simp only [RCLike.star_def, Complex.conj_im] at hi
    apply Complex.ext
    · simp [hermitianOfRealCoordinates, realCoordinatesOfHermitian]
    · simp [hermitianOfRealCoordinates]
      linarith only [hi]
  · have hji := hA.apply j i
    have hre := congrArg Complex.re hji
    have him := congrArg Complex.im hji
    simp only [RCLike.star_def, Complex.conj_re, Complex.conj_im] at hre him
    by_cases hl : i < j
    · apply Complex.ext <;>
        simp [hermitianOfRealCoordinates, realCoordinatesOfHermitian, he, hl,
          hl.le, not_le_of_gt hl] <;> linarith only [hre, him]
    · have hj : j < i := lt_of_le_of_ne (le_of_not_gt hl) (Ne.symm he)
      apply Complex.ext <;>
        simp [hermitianOfRealCoordinates, realCoordinatesOfHermitian, he, hl,
          hj.le, not_le_of_gt hj] <;> linarith only [hre, him]

/-- Continuous encoding on the full n^2-dimensional real coordinate space. -/
theorem continuous_hermitianOfRealCoordinates {n : ℕ} :
    Continuous (hermitianOfRealCoordinates (n := n)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  dsimp [hermitianOfRealCoordinates]
  split_ifs <;> fun_prop

theorem continuous_realCoordinatesOfHermitian {n : ℕ} :
    Continuous (realCoordinatesOfHermitian (n := n)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  dsimp [realCoordinatesOfHermitian]
  split_ifs <;> fun_prop

/-- Explicit Borel equivalence with the Hermitian subspace, in every size. -/
def hermitianRealCoordinateEquiv (n : ℕ) :
    Matrix (Fin n) (Fin n) ℝ ≃ᵐ {A : Matrix (Fin n) (Fin n) ℂ // A.IsHermitian} where
  toFun q := ⟨hermitianOfRealCoordinates q, hermitianOfRealCoordinates_isHermitian q⟩
  invFun A := realCoordinatesOfHermitian A.1
  left_inv := realCoordinates_hermitianOfRealCoordinates
  right_inv A := Subtype.ext (hermitianOfRealCoordinates_realCoordinates A.1 A.2)
  measurable_toFun := continuous_hermitianOfRealCoordinates.subtype_mk
    hermitianOfRealCoordinates_isHermitian |>.measurable
  measurable_invFun := continuous_realCoordinatesOfHermitian.measurable.comp measurable_subtype_coe

/-- Product Lebesgue measure on the n^2 explicitly chosen real coordinates. -/
def hermitianRealCoordinateMeasure (n : ℕ) : Measure (Matrix (Fin n) (Fin n) ℝ) :=
  Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => (volume : Measure ℝ)))

/-- The chosen volume is defined on n^2 real coordinates and then pushed forward.
It is not the restriction of the 2n^2-dimensional complex ambient volume. -/
def hermitianCoordinateVolume (n : ℕ) :
    Measure {A : Matrix (Fin n) (Fin n) ℂ // A.IsHermitian} :=
  (hermitianRealCoordinateMeasure n).map (hermitianRealCoordinateEquiv n)

theorem hermitianRealCoordinateEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (hermitianRealCoordinateEquiv n)
      (hermitianRealCoordinateMeasure n) (hermitianCoordinateVolume n) :=
  ⟨(hermitianRealCoordinateEquiv n).measurable, rfl⟩

theorem hermitianOfRealCoordinates_shift {n : ℕ}
    (q : Matrix (Fin n) (Fin n) ℝ) (x : ℝ) :
    hermitianOfRealCoordinates (q + x • (1 : Matrix (Fin n) (Fin n) ℝ)) =
      hermitianOfRealCoordinates q + (x : ℂ) • 1 := by
  ext i j
  by_cases he : i = j
  · subst j
    simp [hermitianOfRealCoordinates, Matrix.add_apply, Matrix.smul_apply]
  · simp [hermitianOfRealCoordinates, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply, he, Ne.symm he]

end
end JinWishart

#print axioms JinWishart.hermitianOfRealCoordinates_isHermitian
#print axioms JinWishart.realCoordinates_hermitianOfRealCoordinates
#print axioms JinWishart.hermitianOfRealCoordinates_realCoordinates
#print axioms JinWishart.continuous_hermitianOfRealCoordinates
#print axioms JinWishart.continuous_realCoordinatesOfHermitian
#print axioms JinWishart.hermitianRealCoordinateEquiv_measurePreserving
#print axioms JinWishart.hermitianOfRealCoordinates_shift
