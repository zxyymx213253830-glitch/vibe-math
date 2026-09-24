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
