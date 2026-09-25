import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# A probability-measure foundation for Wishart matrices

Mathlib has no named Wishart distribution, but it does provide finite-dimensional Gaussian
measures, matrix measurability, and positive-semidefinite matrix theory.  This file combines
those pieces to define central and noncentral real and complex Wishart laws as pushforwards
under the Gram map.  It does not yet derive their Lebesgue densities or eigenvalue distributions.
-/

open MeasureTheory Matrix ProbabilityTheory
open scoped ComplexOrder

namespace JinWishart

variable {m n : ℕ}

/-- A complex Gaussian sample matrix is encoded by pairs of real Gaussian coordinates. -/
abbrev ComplexSample := EuclideanSpace ℝ ((Fin m × Fin n) × Fin 2)

/-- Complex sample matrix with circular complex Gaussian entries of unit variance. -/
noncomputable def complexSampleMatrix (x : ComplexSample (m := m) (n := n)) :
    Matrix (Fin m) (Fin n) ℂ :=
  fun i j ↦ ((x ((i, j), 0) : ℝ) + Complex.I * x ((i, j), 1)) / Real.sqrt 2

/-- Radial energy of the two real Gaussian coordinates in a `1 × 1` complex
sample. It is the scalar whose law must be identified with the exponential
target in the central scalar Wishart specialization. -/
noncomputable def centralScalarSampleEnergy
    (x : ComplexSample (m := 1) (n := 1)) : ℝ :=
  (x ((0, 0), 0) ^ 2 + x ((0, 0), 1) ^ 2) / 2

/-- Squared Euclidean energy of an `m × 1` central complex Gaussian sample.
This is the scalar Gram entry in the one-column Wishart specialization. -/
noncomputable def centralColumnSampleEnergy {m : ℕ}
    (x : ComplexSample (m := m) (n := 1)) : ℝ :=
  ∑ i : Fin m, (x ((i, 0), 0) ^ 2 + x ((i, 0), 1) ^ 2) / 2

/-- For one column, the explicit sum of coordinate energies is the squared
Euclidean norm of the underlying real sample vector divided by two. -/
theorem centralColumnSampleEnergy_eq_euclideanEnergy {m : ℕ}
    (x : ComplexSample (m := m) (n := 1)) :
    centralColumnSampleEnergy x = ‖x‖ ^ 2 / 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [centralColumnSampleEnergy, Fintype.sum_prod_type, Fin.sum_univ_two]
  rw [Finset.sum_div]

/-- Real-coordinate representation of a deterministic complex mean matrix. -/
noncomputable def complexSampleMean (M : Matrix (Fin m) (Fin n) ℂ) :
    ComplexSample (m := m) (n := n) :=
  WithLp.toLp 2 (fun ij : (Fin m × Fin n) × Fin 2 ↦
    Real.sqrt 2 * if ij.2 = 0 then (M ij.1.1 ij.1.2).re else (M ij.1.1 ij.1.2).im)

theorem complexSampleMatrix_add_mean (x : ComplexSample (m := m) (n := n))
    (M : Matrix (Fin m) (Fin n) ℂ) :
    complexSampleMatrix (x + complexSampleMean M) = complexSampleMatrix x + M := by
  have hsqrt : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  ext i j
  apply Complex.ext
  · simp [complexSampleMatrix, complexSampleMean]
    field_simp [hsqrt]
  · simp [complexSampleMatrix, complexSampleMean]
    field_simp [hsqrt]

/-- Complex Gram matrix `Xᴴ X`. -/
def complexGram (X : Matrix (Fin m) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Xᴴ * X

/-- In the `1 × 1` central model, the Gram entry is the squared radius of the
two real Gaussian coordinates divided by two. This reduces the outstanding
distribution theorem to a two-dimensional radial Gaussian integral. -/
theorem complexGram_centralScalar_entry
    (x : ComplexSample (m := 1) (n := 1)) :
    complexGram (complexSampleMatrix x) 0 0 =
      (centralScalarSampleEnergy x : ℂ) := by
  simp [complexGram, complexSampleMatrix, centralScalarSampleEnergy,
    Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hsqrt : (Real.sqrt (2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
  field_simp [hsqrt]
  have hsq : (Real.sqrt (2 : ℝ) : ℂ) ^ 2 = 2 := by
    exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2))
  rw [hsq]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- In the central one-column model, the scalar Gram matrix entry is the total
coordinate energy for any number of sample rows. -/
theorem complexGram_centralColumn_entry {m : ℕ}
    (x : ComplexSample (m := m) (n := 1)) :
    complexGram (complexSampleMatrix x) 0 0 =
      (centralColumnSampleEnergy x : ℂ) := by
  classical
  have hsqrt : (Real.sqrt (2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2))
  have hsq : (Real.sqrt (2 : ℝ) : ℂ) ^ 2 = 2 := by
    exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2))
  have hrow (i : Fin m) :
    star (complexSampleMatrix x i 0) * complexSampleMatrix x i 0 =
        (((x ((i, 0), 0) ^ 2 + x ((i, 0), 1) ^ 2) / 2 : ℝ) : ℂ) := by
    rw [RCLike.star_def, RCLike.conj_mul]
    norm_cast
    rw [RCLike.norm_sq_eq_def]
    simp [complexSampleMatrix]
    field_simp [hsqrt]
    rw [hsq]
    ring
  simp only [complexGram, Matrix.mul_apply, Matrix.conjTranspose_apply]
  calc
    _ = ∑ i : Fin m,
        (((x ((i, 0), 0) ^ 2 + x ((i, 0), 1) ^ 2) / 2 : ℝ) : ℂ) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hrow i
    _ = (centralColumnSampleEnergy x : ℂ) := by
          simp [centralColumnSampleEnergy]

/-- Every complex Gram matrix is Hermitian positive semidefinite. -/
theorem complexGram_posSemidef (X : Matrix (Fin m) (Fin n) ℂ) :
    (complexGram X).PosSemidef := by
  exact Matrix.posSemidef_conjTranspose_mul_self X

/-- The descending eigenvalue list of a complex Gram matrix is nonnegative.
This is the deterministic spectral fact needed before defining the ordered
Wishart eigenvalue random variables in the distribution formulas. -/
theorem complexGram_eigenvalues₀_nonneg
    (X : Matrix (Fin m) (Fin n) ℂ) (i : Fin (Fintype.card (Fin n))) :
    0 ≤ (complexGram_posSemidef X).1.eigenvalues₀ i := by
  have hpsd : (complexGram X).PosSemidef := complexGram_posSemidef X
  let j : Fin n :=
    Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n))) i
  have hj := hpsd.eigenvalues_nonneg j
  simpa [j, Matrix.IsHermitian.eigenvalues, Matrix.IsHermitian.eigenvalues₀] using hj

/-- mathlib indexes Hermitian eigenvalues in descending order. -/
theorem complexGram_eigenvalues₀_antitone
    (X : Matrix (Fin m) (Fin n) ℂ) :
    Antitone (complexGram_posSemidef X).1.eigenvalues₀ := by
  exact (complexGram_posSemidef X).1.eigenvalues₀_antitone

/-- The ordered eigenvalues of every shifted complex Gaussian Gram sample remain
nonnegative; this is the pointwise spectral statement for noncentral Wishart. -/
theorem complexNoncentralGram_eigenvalues₀_nonneg
    (M : Matrix (Fin m) (Fin n) ℂ)
    (x : ComplexSample (m := m) (n := n)) (i : Fin (Fintype.card (Fin n))) :
    0 ≤ (complexGram_posSemidef (complexSampleMatrix x + M)).1.eigenvalues₀ i :=
  complexGram_eigenvalues₀_nonneg (complexSampleMatrix x + M) i

noncomputable def complexSampleGram (x : ComplexSample (m := m) (n := n)) :
    Matrix (Fin n) (Fin n) ℂ :=
  complexGram (complexSampleMatrix x)

@[fun_prop]
theorem measurable_complexSampleGram :
    Measurable (complexSampleGram (m := m) (n := n)) := by
  apply Measurable.of_eval_matrix
  intro i j
  simp only [complexSampleGram, complexGram, complexSampleMatrix, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  fun_prop

theorem measurable_shiftedComplexSampleGram (M : Matrix (Fin m) (Fin n) ℂ) :
    Measurable (fun x : ComplexSample (m := m) (n := n) ↦
      complexGram (complexSampleMatrix x + M)) := by
  have h : (fun x : ComplexSample (m := m) (n := n) ↦
      complexGram (complexSampleMatrix x + M)) =
      (fun x ↦ complexSampleGram (x + complexSampleMean M)) := by
    funext x
    rw [← complexSampleMatrix_add_mean x M]
    rfl
  rw [h]
  exact measurable_complexSampleGram.comp (by fun_prop)

/-- Central complex Wishart law with identity scale, defined as the Gram pushforward of a
standard circular complex Gaussian matrix. -/
noncomputable def complexWishart : Measure (Matrix (Fin n) (Fin n) ℂ) :=
  (stdGaussian (ComplexSample (m := m) (n := n))).map complexSampleGram

instance isProbabilityMeasure_complexWishart :
    IsProbabilityMeasure (complexWishart (m := m) (n := n)) := by
  rw [complexWishart]
  infer_instance

/-- Noncentral complex Wishart law with identity scale and mean matrix `M`. -/
noncomputable def complexNoncentralWishart (M : Matrix (Fin m) (Fin n) ℂ) :
    Measure (Matrix (Fin n) (Fin n) ℂ) :=
  (stdGaussian (ComplexSample (m := m) (n := n))).map
    (fun x ↦ complexGram (complexSampleMatrix x + M))

instance isProbabilityMeasure_complexNoncentralWishart (M : Matrix (Fin m) (Fin n) ℂ) :
    IsProbabilityMeasure (complexNoncentralWishart (m := m) (n := n) M) := by
  rw [complexNoncentralWishart]
  infer_instance

theorem complexWishart_measure_posSemidef :
    (complexWishart (m := m) (n := n)) {W | W.PosSemidef} = 1 := by
  rw [complexWishart, Measure.map_apply measurable_complexSampleGram
    (Matrix.posSemidef_is_closed.measurableSet)]
  have hpre : (complexSampleGram (m := m) (n := n)) ⁻¹'
      {W : Matrix (Fin n) (Fin n) ℂ | W.PosSemidef} = Set.univ := by
    ext x
    simp [complexSampleGram, complexGram_posSemidef]
  rw [hpre, measure_univ]

theorem complexNoncentralWishart_measure_posSemidef (M : Matrix (Fin m) (Fin n) ℂ) :
    (complexNoncentralWishart (m := m) (n := n) M) {W | W.PosSemidef} = 1 := by
  rw [complexNoncentralWishart, Measure.map_apply (measurable_shiftedComplexSampleGram M)
    (Matrix.posSemidef_is_closed.measurableSet)]
  have hpre : (fun x : ComplexSample (m := m) (n := n) ↦
      complexGram (complexSampleMatrix x + M)) ⁻¹'
      {W : Matrix (Fin n) (Fin n) ℂ | W.PosSemidef} = Set.univ := by
    ext x
    simp [complexGram_posSemidef]
  rw [hpre, measure_univ]

/-- Event that a matrix lies above threshold `x` in Loewner order, encoded as a shifted PSD cone.
For Hermitian matrices, the theorems below identify this with a lower bound on every eigenvalue
and, in nonzero dimension, with a lower bound on the final entry of the descending eigenvalue list. -/
def smallestEigenvalueTailEvent (x : ℝ) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {W | (W - (x : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef}

/-- Spectral characterization of the shifted-PSD event. -/
theorem smallestEigenvalueTailEvent_iff_eigenvalues_ge
    (W : Matrix (Fin n) (Fin n) ℂ) (hW : W.IsHermitian) (x : ℝ) :
    W ∈ smallestEigenvalueTailEvent x ↔ ∀ i, x ≤ hW.eigenvalues i := by
  change (W - (x : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef ↔ _
  let U := hW.eigenvectorUnitary
  let D : Matrix (Fin n) (Fin n) ℂ := diagonal (Complex.ofReal ∘ hW.eigenvalues)
  let Φ := Unitary.conjStarAlgAut ℂ (Matrix (Fin n) (Fin n) ℂ) U
  have hspec : W = Φ D := by
    simpa [Φ, U, D] using hW.spectral_theorem
  have hmap : Φ D - (x : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) =
      Φ (D - (x : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    rw [map_sub]
    rw [map_smul, map_one]
  have hdiag : D - (x : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) =
      diagonal (fun i => Complex.ofReal (hW.eigenvalues i - x)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D, Complex.ofReal_sub]
    · simp [D, hij]
  calc
    W ∈ smallestEigenvalueTailEvent x ↔
        (Φ D - (x : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef := by
      change (W - (x : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef ↔ _
      rw [hspec]
    _ ↔ (D - (x : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef := by
      rw [hmap]
      simp only [Φ, Unitary.conjStarAlgAut_apply]
      exact (Unitary.isUnit_coe (U := U)).posSemidef_star_right_conjugate_iff
    _ ↔ ∀ i, x ≤ hW.eigenvalues i := by
      rw [hdiag, Matrix.posSemidef_diagonal_iff]
      simp only [Complex.zero_le_real, sub_nonneg]

/-- Reindex the all-eigenvalues condition through mathlib's canonical descending list. -/
theorem all_eigenvalues_ge_iff_eigenvalues₀_ge
    (W : Matrix (Fin n) (Fin n) ℂ) (hW : W.IsHermitian) (x : ℝ) :
    (∀ i : Fin n, x ≤ hW.eigenvalues i) ↔
      ∀ i : Fin (Fintype.card (Fin n)), x ≤ hW.eigenvalues₀ i := by
  let e : Fin n ≃ Fin (Fintype.card (Fin n)) :=
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))).symm
  constructor
  · intro h i
    have hi := h (e.symm i)
    simpa [e, Matrix.IsHermitian.eigenvalues] using hi
  · intro h i
    have hi := h (e i)
    simpa [e, Matrix.IsHermitian.eigenvalues] using hi

/-- The shifted-PSD event is exactly a lower bound on the full descending eigenvalue list. -/
theorem smallestEigenvalueTailEvent_iff_eigenvalues₀_ge
    (W : Matrix (Fin n) (Fin n) ℂ) (hW : W.IsHermitian) (x : ℝ) :
    W ∈ smallestEigenvalueTailEvent x ↔
      ∀ i : Fin (Fintype.card (Fin n)), x ≤ hW.eigenvalues₀ i :=
  (smallestEigenvalueTailEvent_iff_eigenvalues_ge W hW x).trans
    (all_eigenvalues_ge_iff_eigenvalues₀_ge W hW x)

private theorem forall_fin_ge_iff_max {N : ℕ} (f : Fin N → ℝ) (hf : Antitone f)
    (imax : Fin N) (hmax : ∀ i, i ≤ imax) (x : ℝ) :
    (∀ i, x ≤ f i) ↔ x ≤ f imax := by
  constructor
  · intro h
    exact h imax
  · intro h i
    exact le_trans h (hf (hmax i))

/-- For a nonempty matrix, the event is equivalent to a bound on the smallest
entry of mathlib's descending eigenvalue list (`Fin.last`). -/
theorem smallestEigenvalueTailEvent_iff_smallest_eigenvalue₀_ge
    (W : Matrix (Fin n) (Fin n) ℂ) (hW : W.IsHermitian)
    (hN : 0 < Fintype.card (Fin n)) (x : ℝ) :
    W ∈ smallestEigenvalueTailEvent x ↔
      x ≤ hW.eigenvalues₀
        (Fin.cast (Nat.sub_add_cancel hN) (Fin.last (Fintype.card (Fin n) - 1))) := by
  rw [smallestEigenvalueTailEvent_iff_eigenvalues₀_ge]
  let N := Fintype.card (Fin n)
  let imax : Fin N := Fin.cast (Nat.sub_add_cancel hN) (Fin.last (N - 1))
  have hmax : ∀ i : Fin N, i ≤ imax := by
    intro i
    apply Fin.le_iff_val_le_val.mpr
    simp [imax]
    omega
  exact forall_fin_ge_iff_max hW.eigenvalues₀ hW.eigenvalues₀_antitone imax hmax x

/-- Event that a Hermitian matrix is bounded above by `x I` in Loewner order. -/
def largestEigenvalueCdfEvent (x : ℝ) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {W | ((x : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - W).PosSemidef}

/-- Spectral characterization of the Loewner upper-bound event. -/
theorem largestEigenvalueCdfEvent_iff_eigenvalues_le
    (W : Matrix (Fin n) (Fin n) ℂ) (hW : W.IsHermitian) (x : ℝ) :
    W ∈ largestEigenvalueCdfEvent x ↔ ∀ i, hW.eigenvalues i ≤ x := by
  change ((x : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - W).PosSemidef ↔ _
  let U := hW.eigenvectorUnitary
  let D : Matrix (Fin n) (Fin n) ℂ := diagonal (Complex.ofReal ∘ hW.eigenvalues)
  let Φ := Unitary.conjStarAlgAut ℂ (Matrix (Fin n) (Fin n) ℂ) U
  have hspec : W = Φ D := by
    simpa [Φ, U, D] using hW.spectral_theorem
  have hmap : (x : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - Φ D =
      Φ ((x : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - D) := by
    rw [map_sub]
    rw [map_smul, map_one]
  have hdiag : (x : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - D =
      diagonal (fun i => Complex.ofReal (x - hW.eigenvalues i)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D, Complex.ofReal_sub]
    · simp [D, hij]
  calc
    W ∈ largestEigenvalueCdfEvent x ↔
        ((x : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - Φ D).PosSemidef := by
      change ((x : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - W).PosSemidef ↔ _
      rw [hspec]
    _ ↔ ((x : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - D).PosSemidef := by
      rw [hmap]
      simp only [Φ, Unitary.conjStarAlgAut_apply]
      exact (Unitary.isUnit_coe (U := U)).posSemidef_star_right_conjugate_iff
    _ ↔ ∀ i, hW.eigenvalues i ≤ x := by
      rw [hdiag, Matrix.posSemidef_diagonal_iff]
      simp only [Complex.zero_le_real, sub_nonneg]

/-- Reindex the all-eigenvalues upper-bound condition through mathlib's descending list. -/
theorem all_eigenvalues_le_iff_eigenvalues₀_le
    (W : Matrix (Fin n) (Fin n) ℂ) (hW : W.IsHermitian) (x : ℝ) :
    (∀ i : Fin n, hW.eigenvalues i ≤ x) ↔
      ∀ i : Fin (Fintype.card (Fin n)), hW.eigenvalues₀ i ≤ x := by
  let e : Fin n ≃ Fin (Fintype.card (Fin n)) :=
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))).symm
  constructor
  · intro h i
    have hi := h (e.symm i)
    simpa [e, Matrix.IsHermitian.eigenvalues] using hi
  · intro h i
    have hi := h (e i)
    simpa [e, Matrix.IsHermitian.eigenvalues] using hi

private theorem forall_fin_le_iff_zero {N : ℕ} (f : Fin N → ℝ)
    (hf : Antitone f) (i0 : Fin N) (hmin : ∀ i, i0 ≤ i) (x : ℝ) :
    (∀ i, f i ≤ x) ↔ f i0 ≤ x := by
  constructor
  · intro h
    exact h i0
  · intro h i
    exact le_trans (hf (hmin i)) h

/-- In nonzero dimension, the Loewner upper-bound event is equivalent to a bound on
the first (largest) entry of mathlib's descending eigenvalue list. -/
theorem largestEigenvalueCdfEvent_iff_largest_eigenvalue₀_le
    (W : Matrix (Fin n) (Fin n) ℂ) (hW : W.IsHermitian)
    (hN : 0 < Fintype.card (Fin n)) (x : ℝ) :
    W ∈ largestEigenvalueCdfEvent x ↔
      hW.eigenvalues₀ (⟨0, by omega⟩ : Fin (Fintype.card (Fin n))) ≤ x := by
  rw [largestEigenvalueCdfEvent_iff_eigenvalues_le,
    all_eigenvalues_le_iff_eigenvalues₀_le]
  exact forall_fin_le_iff_zero hW.eigenvalues₀ hW.eigenvalues₀_antitone
    ⟨0, by omega⟩ (by
      intro i
      apply Fin.le_iff_val_le_val.mpr
      simp) x

/-- The largest-eigenvalue CDF event is measurable as a preimage of the closed PSD cone. -/
theorem measurableSet_largestEigenvalueCdfEvent (x : ℝ) :
    MeasurableSet (largestEigenvalueCdfEvent (n := n) x) := by
  have hmap : Measurable
      (fun W : Matrix (Fin n) (Fin n) ℂ =>
        (x : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - W) := by
    fun_prop
  exact Matrix.posSemidef_is_closed.measurableSet.preimage hmap

/-- Probability of the largest-eigenvalue CDF event under the noncentral Wishart pushforward. -/
noncomputable def complexNoncentralWishartLargestEigenvalueCdf
    (M : Matrix (Fin m) (Fin n) ℂ) (x : ℝ) : ENNReal :=
  complexNoncentralWishart (m := m) (n := n) M (largestEigenvalueCdfEvent x)

theorem measurableSet_smallestEigenvalueTailEvent (x : ℝ) :
    MeasurableSet (smallestEigenvalueTailEvent (n := n) x) := by
  have hmap : Measurable
      (fun W : Matrix (Fin n) (Fin n) ℂ =>
        W - (x : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    fun_prop
  exact Matrix.posSemidef_is_closed.measurableSet.preimage hmap

/-- Index of the smallest entry in mathlib's descending eigenvalue list. -/
noncomputable def smallestEigenvalue₀Index (hn : 0 < n) :
    Fin (Fintype.card (Fin n)) := by
  have hN : 0 < Fintype.card (Fin n) := by simpa using hn
  exact Fin.cast (Nat.sub_add_cancel hN)
    (Fin.last (Fintype.card (Fin n) - 1))

/-- The least eigenvalue of a noncentral complex Gram sample. The positive-dimension
hypothesis is needed because an empty matrix has no smallest eigenvalue. -/
noncomputable def complexNoncentralSampleSmallestEigenvalue
    (M : Matrix (Fin m) (Fin n) ℂ) (hn : 0 < n)
    (x : ComplexSample (m := m) (n := n)) : ℝ :=
  (complexGram_posSemidef (complexSampleMatrix x + M)).1.eigenvalues₀
    (smallestEigenvalue₀Index hn)

/-- In the `1 × 1` central model, the only ordered eigenvalue is exactly the
two-coordinate radial energy. Thus the remaining scalar distribution step is
precisely the law of this squared Gaussian radius. -/
theorem centralScalarSampleSmallestEigenvalue_eq_energy
    (x : ComplexSample (m := 1) (n := 1)) :
    complexNoncentralSampleSmallestEigenvalue (0 : Matrix (Fin 1) (Fin 1) ℂ)
      (by norm_num) x = centralScalarSampleEnergy x := by
  let W : Matrix (Fin 1) (Fin 1) ℂ := complexGram (complexSampleMatrix x)
  let hW : W.IsHermitian := (complexGram_posSemidef (complexSampleMatrix x)).1
  have htrace := hW.trace_eq_sum_eigenvalues
  have heig : W 0 0 = (hW.eigenvalues 0 : ℂ) := by
    simpa [Matrix.trace] using htrace
  have hentry : W 0 0 = (centralScalarSampleEnergy x : ℂ) := by
    simpa [W] using complexGram_centralScalar_entry x
  have hreal : centralScalarSampleEnergy x = hW.eigenvalues 0 :=
    Complex.ofReal_injective (hentry.symm.trans heig)
  simp only [complexNoncentralSampleSmallestEigenvalue, add_zero]
  change hW.eigenvalues₀ (smallestEigenvalue₀Index (n := 1) (by norm_num)) = _
  have hidx : smallestEigenvalue₀Index (n := 1) (by norm_num) =
      (Fintype.equivOfCardEq (Fintype.card_fin 1)).symm (0 : Fin 1) := by
    apply Fin.ext
    simp [smallestEigenvalue₀Index]
  rw [hidx]
  change hW.eigenvalues 0 = centralScalarSampleEnergy x
  exact hreal.symm

/-- The only ordered eigenvalue of a one-column Gram sample is its scalar
energy, for any positive number of sample rows. -/
theorem centralColumnSampleSmallestEigenvalue_eq_energy {m : ℕ} (hm : 0 < m)
    (x : ComplexSample (m := m) (n := 1)) :
    complexNoncentralSampleSmallestEigenvalue (0 : Matrix (Fin m) (Fin 1) ℂ)
      (by norm_num) x = centralColumnSampleEnergy x := by
  let W : Matrix (Fin 1) (Fin 1) ℂ := complexGram (complexSampleMatrix x)
  let hW : W.IsHermitian := (complexGram_posSemidef (complexSampleMatrix x)).1
  have htrace := hW.trace_eq_sum_eigenvalues
  have heig : W 0 0 = (hW.eigenvalues 0 : ℂ) := by
    simpa [Matrix.trace] using htrace
  have hentry : W 0 0 = (centralColumnSampleEnergy x : ℂ) := by
    simpa [W] using complexGram_centralColumn_entry x
  have hreal : centralColumnSampleEnergy x = hW.eigenvalues 0 :=
    Complex.ofReal_injective (hentry.symm.trans heig)
  simp only [complexNoncentralSampleSmallestEigenvalue, add_zero]
  change hW.eigenvalues₀ (smallestEigenvalue₀Index (n := 1) (by norm_num)) = _
  have hidx : smallestEigenvalue₀Index (n := 1) (by norm_num) =
      (Fintype.equivOfCardEq (Fintype.card_fin 1)).symm (0 : Fin 1) := by
    apply Fin.ext
    simp [smallestEigenvalue₀Index]
  rw [hidx]
  change hW.eigenvalues 0 = centralColumnSampleEnergy x
  exact hreal.symm

/-- The smallest ordered eigenvalue of a shifted complex Gram sample is measurable.
The proof uses measurable shifted-PSD sublevel events rather than a general eigenvalue
continuity theorem. -/
theorem measurable_complexNoncentralSampleSmallestEigenvalue
    (M : Matrix (Fin m) (Fin n) ℂ) (hn : 0 < n) :
    Measurable (complexNoncentralSampleSmallestEigenvalue M hn) := by
  apply measurable_of_Iio
  intro x
  have hpre :
      (complexNoncentralSampleSmallestEigenvalue M hn) ⁻¹' Set.Iio x =
        (fun z : ComplexSample (m := m) (n := n) =>
          complexGram (complexSampleMatrix z + M)) ⁻¹'
      (smallestEigenvalueTailEvent x)ᶜ := by
    ext z
    have hspec := smallestEigenvalueTailEvent_iff_smallest_eigenvalue₀_ge
      (complexGram (complexSampleMatrix z + M))
      (complexGram_posSemidef (complexSampleMatrix z + M)).1
      (by simpa using hn) x
    change complexNoncentralSampleSmallestEigenvalue M hn z < x ↔ _
    change complexNoncentralSampleSmallestEigenvalue M hn z < x ↔
      complexGram (complexSampleMatrix z + M) ∉ smallestEigenvalueTailEvent x
    rw [hspec]
    exact lt_iff_not_ge
  rw [hpre]
  exact (measurableSet_smallestEigenvalueTailEvent x).compl.preimage
    (measurable_shiftedComplexSampleGram M)

/-- Probability of the measurable shifted-PSD event. For `n > 0`, the spectral theorem above
identifies it with `P(λ_min ≥ x)`. Turning its complement into the paper's `≤` CDF still requires
a no-atoms proof. -/
noncomputable def complexNoncentralWishartSmallestEigenvalueTail
    (M : Matrix (Fin m) (Fin n) ℂ) (x : ℝ) : ENNReal :=
  complexNoncentralWishart (m := m) (n := n) M (smallestEigenvalueTailEvent x)

theorem complexNoncentralWishartSmallestEigenvalueTail_zero
    (M : Matrix (Fin m) (Fin n) ℂ) :
    complexNoncentralWishartSmallestEigenvalueTail (m := m) (n := n) M 0 = 1 := by
  simpa [complexNoncentralWishartSmallestEigenvalueTail, smallestEigenvalueTailEvent] using
    complexNoncentralWishart_measure_posSemidef (m := m) (n := n) M

/-- The strict CDF of the sample least eigenvalue is the complement of the
Wishart shifted-PSD tail event. This is an exact pushforward identity; converting
the strict CDF to the weak CDF still requires showing the level set is null. -/
theorem complexNoncentralSampleSmallestEigenvalue_strictCDF_eq_one_sub_tail
    (M : Matrix (Fin m) (Fin n) ℂ) (hn : 0 < n) (x : ℝ) :
    stdGaussian (ComplexSample (m := m) (n := n))
        {z | complexNoncentralSampleSmallestEigenvalue M hn z < x} =
      1 - complexNoncentralWishartSmallestEigenvalueTail M x := by
  let G : ComplexSample (m := m) (n := n) → Matrix (Fin n) (Fin n) ℂ :=
    fun z => complexGram (complexSampleMatrix z + M)
  have hG : Measurable G := measurable_shiftedComplexSampleGram M
  have hpre : {z | complexNoncentralSampleSmallestEigenvalue M hn z < x} =
      (G ⁻¹' smallestEigenvalueTailEvent x)ᶜ := by
    ext z
    have hspec := smallestEigenvalueTailEvent_iff_smallest_eigenvalue₀_ge
      (G z) (complexGram_posSemidef (complexSampleMatrix z + M)).1
      (by simpa using hn) x
    change complexNoncentralSampleSmallestEigenvalue M hn z < x ↔ _
    change complexNoncentralSampleSmallestEigenvalue M hn z < x ↔
      G z ∉ smallestEigenvalueTailEvent x
    rw [hspec]
    exact lt_iff_not_ge
  have hmeas : MeasurableSet (smallestEigenvalueTailEvent x) :=
    measurableSet_smallestEigenvalueTailEvent (n := n) x
  calc
    stdGaussian (ComplexSample (m := m) (n := n))
        {z | complexNoncentralSampleSmallestEigenvalue M hn z < x} =
      stdGaussian (ComplexSample (m := m) (n := n))
        (G ⁻¹' smallestEigenvalueTailEvent x)ᶜ := by rw [hpre]
    _ = 1 - stdGaussian (ComplexSample (m := m) (n := n))
        (G ⁻¹' smallestEigenvalueTailEvent x) := by
          rw [measure_compl (hmeas.preimage hG) (measure_ne_top _ _)]
          simp
    _ = 1 - complexNoncentralWishartSmallestEigenvalueTail M x := by
          rw [complexNoncentralWishartSmallestEigenvalueTail,
            complexNoncentralWishart, Measure.map_apply hG hmeas]

/-- A real Gaussian sample matrix is represented by a vector in a finite-dimensional Euclidean
space, avoiding the need to equip the raw matrix type with an inner-product structure. -/
abbrev Sample := EuclideanSpace ℝ (Fin m × Fin n)

/-- The Gram matrix of a real `m × n` sample matrix. -/
def realGram (X : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Xᴴ * X

def sampleMatrix (x : Sample (m := m) (n := n)) : Matrix (Fin m) (Fin n) ℝ :=
  fun i j ↦ x (i, j)

/-- Embed a deterministic matrix mean into the sample Euclidean space. -/
def sampleMean (M : Matrix (Fin m) (Fin n) ℝ) : Sample (m := m) (n := n) :=
  WithLp.toLp 2 (fun ij : Fin m × Fin n ↦ M ij.1 ij.2)

def sampleGram (x : Sample (m := m) (n := n)) : Matrix (Fin n) (Fin n) ℝ :=
  realGram (sampleMatrix x)

@[fun_prop]
theorem measurable_sampleGram : Measurable (sampleGram (m := m) (n := n)) := by
  apply Measurable.of_eval_matrix
  intro i j
  simp only [sampleGram, sampleMatrix, realGram, Matrix.mul_apply,
    Matrix.conjTranspose_apply, star_trivial]
  fun_prop

theorem measurable_shiftedSampleGram (M : Matrix (Fin m) (Fin n) ℝ) :
    Measurable (fun x : Sample (m := m) (n := n) ↦ sampleGram (x + sampleMean M)) := by
  exact measurable_sampleGram.comp (by fun_prop)

theorem sampleMatrix_add_sampleMean (x : Sample (m := m) (n := n))
    (M : Matrix (Fin m) (Fin n) ℝ) :
    sampleMatrix (x + sampleMean M) = sampleMatrix x + M := by
  ext i j
  simp [sampleMatrix, sampleMean]

/-- Every real Gram matrix is positive semidefinite. -/
theorem realGram_posSemidef (X : Matrix (Fin m) (Fin n) ℝ) :
    (realGram X).PosSemidef := by
  exact Matrix.posSemidef_conjTranspose_mul_self X

/-- Central real Wishart law with `m` degrees of freedom and identity scale.
It is the pushforward of a standard Gaussian `m × n` sample matrix by `X ↦ Xᵀ X`. -/
noncomputable def realWishart :
  Measure (Matrix (Fin n) (Fin n) ℝ) :=
  (stdGaussian (Sample (m := m) (n := n))).map sampleGram

instance isProbabilityMeasure_realWishart : IsProbabilityMeasure (realWishart (m := m) (n := n)) := by
  rw [realWishart]
  infer_instance

/-- Noncentral real Wishart law with identity scale and deterministic mean matrix `M`. -/
noncomputable def realNoncentralWishart (M : Matrix (Fin m) (Fin n) ℝ) :
  Measure (Matrix (Fin n) (Fin n) ℝ) :=
  (stdGaussian (Sample (m := m) (n := n))).map (fun x ↦ sampleGram (x + sampleMean M))

instance isProbabilityMeasure_realNoncentralWishart (M : Matrix (Fin m) (Fin n) ℝ) :
    IsProbabilityMeasure (realNoncentralWishart (m := m) (n := n) M) := by
  rw [realNoncentralWishart]
  infer_instance

/-- The central Wishart law assigns probability one to the positive-semidefinite cone. -/
theorem realWishart_measure_posSemidef :
    (realWishart (m := m) (n := n)) {W | W.PosSemidef} = 1 := by
  rw [realWishart, Measure.map_apply measurable_sampleGram
    (Matrix.posSemidef_is_closed.measurableSet)]
  have hpre : (sampleGram (m := m) (n := n)) ⁻¹'
      {W : Matrix (Fin n) (Fin n) ℝ | W.PosSemidef} = Set.univ := by
    ext x
    simp [sampleGram, realGram_posSemidef]
  rw [hpre, measure_univ]

/-- The noncentral Wishart law also assigns probability one to the positive-semidefinite cone. -/
theorem realNoncentralWishart_measure_posSemidef (M : Matrix (Fin m) (Fin n) ℝ) :
    (realNoncentralWishart (m := m) (n := n) M) {W | W.PosSemidef} = 1 := by
  rw [realNoncentralWishart, Measure.map_apply (measurable_shiftedSampleGram M)
    (Matrix.posSemidef_is_closed.measurableSet)]
  have hpre : (fun x : Sample (m := m) (n := n) ↦ sampleGram (x + sampleMean M)) ⁻¹'
      {W : Matrix (Fin n) (Fin n) ℝ | W.PosSemidef} = Set.univ := by
    ext x
    simp [sampleGram, realGram_posSemidef]
  rw [hpre, measure_univ]

end JinWishart
