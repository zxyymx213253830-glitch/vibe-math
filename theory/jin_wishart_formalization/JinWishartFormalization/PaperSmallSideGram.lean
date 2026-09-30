import JinWishartFormalization.WishartProbability
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# The paper's small-side Gram matrix

For a rectangular complex sample matrix `X : Matrix (Fin m) (Fin n) ℂ`, the smaller of
`X * Xᴴ` and `Xᴴ * X` has dimension `min m n`. This file constructs that matrix on the
uniform index type `Fin (min m n)`. It proves pointwise positive semidefiniteness and
measurability for the shifted complex Gaussian sample. No claim about correspondence of the
nonzero spectra of the two Gram matrices is made here.
-/

open MeasureTheory Matrix ProbabilityTheory
open scoped ComplexOrder

namespace JinWishart

variable {m n : ℕ}

/-- Reindex `Fin (min m n)` as `Fin m` in the tall-row/small-row branch. -/
def finMinEquivLeft (hmn : m ≤ n) : Fin (min m n) ≃ Fin m :=
  Equiv.cast (congrArg Fin (Nat.min_eq_left hmn))

/-- Reindex `Fin (min m n)` as `Fin n` in the tall-column/small-column branch. -/
def finMinEquivRight (hnm : n ≤ m) : Fin (min m n) ≃ Fin n :=
  Equiv.cast (congrArg Fin (Nat.min_eq_right hnm))

/-- The small-side Gram matrix: use `X Xᴴ` if rows are the smaller side, and `Xᴴ X`
otherwise, reindexed to the common dimension `min m n`. -/
noncomputable def paperSmallSideGram (X : Matrix (Fin m) (Fin n) ℂ) :
    Matrix (Fin (min m n)) (Fin (min m n)) ℂ := by
  classical
  exact if hmn : m ≤ n then
    (X * Xᴴ).submatrix (finMinEquivLeft hmn) (finMinEquivLeft hmn)
  else
    (Xᴴ * X).submatrix
      (finMinEquivRight (le_of_not_ge hmn)) (finMinEquivRight (le_of_not_ge hmn))

/-- Reindexing a square matrix by an equivalence does not change its
characteristic polynomial. -/
theorem charpoly_submatrix_equiv {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : κ ≃ ι) (A : Matrix ι ι ℂ) :
    (A.submatrix e e).charpoly = A.charpoly := by
  have h := Matrix.charpoly_reindex e.symm A
  rwa [Matrix.reindex_apply, Equiv.symm_symm] at h

/-- Both Gram orientations are PSD, and PSD is preserved by the finite reindexing. -/
theorem paperSmallSideGram_posSemidef (X : Matrix (Fin m) (Fin n) ℂ) :
    (paperSmallSideGram X).PosSemidef := by
  classical
  by_cases hmn : m ≤ n
  · simpa [paperSmallSideGram, hmn] using
      (Matrix.posSemidef_self_mul_conjTranspose X).submatrix (finMinEquivLeft hmn)
  · have hnm : n ≤ m := le_of_not_ge hmn
    simpa [paperSmallSideGram, hmn] using
      (Matrix.posSemidef_conjTranspose_mul_self X).submatrix (finMinEquivRight hnm)

private theorem measurable_submatrix_map {α ι κ : Type*} [MeasurableSpace α]
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    {g : α → Matrix ι ι ℂ} (hg : Measurable g) (e : κ ≃ ι) :
    Measurable (fun x => (g x).submatrix e e) := by
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro j
  simpa [Matrix.submatrix_apply] using
    (measurable_pi_iff.mp (measurable_pi_iff.mp hg (e i)) (e j))

/-- Real-coordinate transformation inducing conjugate transpose of the complex sample matrix. -/
noncomputable def complexSampleConjTranspose
    (z : ComplexSample (m := m) (n := n)) : ComplexSample (m := n) (n := m) :=
  WithLp.toLp 2 (fun ij : (Fin n × Fin m) × Fin 2 =>
    if ij.2 = 0 then z ((ij.1.2, ij.1.1), 0) else -z ((ij.1.2, ij.1.1), 1))

theorem complexSampleMatrix_conjTranspose (z : ComplexSample (m := m) (n := n)) :
    complexSampleMatrix (complexSampleConjTranspose z) = (complexSampleMatrix z)ᴴ := by
  ext i j
  apply Complex.ext <;>
    simp [complexSampleMatrix, complexSampleConjTranspose, Matrix.conjTranspose_apply] <;> ring

theorem measurable_complexSampleConjTranspose :
    Measurable (complexSampleConjTranspose (m := m) (n := n)) := by
  let I := (Fin n × Fin m) × Fin 2
  have hcoe : Measurable (fun z : ComplexSample (m := m) (n := n) => z.ofLp) :=
    (EuclideanSpace.equiv ((Fin m × Fin n) × Fin 2) ℝ).continuous.measurable
  have hcoord : Measurable (fun z : ComplexSample (m := m) (n := n) =>
      fun ij : I =>
        if ij.2 = 0 then z.ofLp ((ij.1.2, ij.1.1), 0)
        else -z.ofLp ((ij.1.2, ij.1.1), 1)) := by
    apply measurable_pi_iff.mpr
    intro ij
    by_cases h : ij.2 = 0
    · simpa only [if_pos h] using (measurable_pi_iff.mp hcoe ((ij.1.2, ij.1.1), 0))
    · have hneg : Measurable (fun z : ComplexSample (m := m) (n := n) =>
          -z.ofLp ((ij.1.2, ij.1.1), 1)) := by
        have hfun : (fun z : ComplexSample (m := m) (n := n) =>
            -z.ofLp ((ij.1.2, ij.1.1), 1)) =
            -(fun z : ComplexSample (m := m) (n := n) =>
              z.ofLp ((ij.1.2, ij.1.1), 1)) := by
          funext z
          rfl
        rw [hfun]
        exact (measurable_pi_iff.mp hcoe ((ij.1.2, ij.1.1), 1)).neg
      simpa only [if_neg h] using hneg
  have htoLp : Measurable (WithLp.toLp 2 : (I → ℝ) →
      ComplexSample (m := n) (n := m)) :=
    (EuclideanSpace.equiv I ℝ).symm.continuous.measurable
  exact htoLp.comp hcoord

private theorem measurable_shiftedRowGram (M : Matrix (Fin m) (Fin n) ℂ) :
    Measurable (fun z : ComplexSample (m := m) (n := n) =>
      (complexSampleMatrix z + M) * (complexSampleMatrix z + M)ᴴ) := by
  have htrans : Measurable (fun z : ComplexSample (m := m) (n := n) =>
      complexSampleConjTranspose (z + complexSampleMean M)) :=
    measurable_complexSampleConjTranspose.comp (by fun_prop)
  have hEq : (fun z : ComplexSample (m := m) (n := n) =>
      (complexSampleMatrix z + M) * (complexSampleMatrix z + M)ᴴ) =
      (fun z => complexSampleGram
        (complexSampleConjTranspose (z + complexSampleMean M))) := by
    funext z
    simp only [complexSampleGram, complexGram, complexSampleMatrix_conjTranspose,
      complexSampleMatrix_add_mean, Matrix.conjTranspose_conjTranspose]
  rw [hEq]
  exact measurable_complexSampleGram.comp htrans

/-- The paper-oriented small-side Gram matrix of a shifted complex Gaussian sample is
measurable as a matrix-valued function of the real Gaussian coordinates. -/
theorem measurable_shiftedPaperSmallSideGram (M : Matrix (Fin m) (Fin n) ℂ) :
    Measurable (fun z : ComplexSample (m := m) (n := n) =>
      paperSmallSideGram (complexSampleMatrix z + M)) := by
  classical
  by_cases hmn : m ≤ n
  · have hsub := measurable_submatrix_map (measurable_shiftedRowGram M) (finMinEquivLeft hmn)
    simpa only [paperSmallSideGram, dif_pos hmn] using hsub
  · have hnm : n ≤ m := le_of_not_ge hmn
    have hsub := measurable_submatrix_map (measurable_shiftedComplexSampleGram M)
      (finMinEquivRight hnm)
    simpa only [paperSmallSideGram, dif_neg hmn, complexGram] using hsub

/-- The actual shifted small-side Gram map, viewed as a measurable map into the subtype of
Hermitian PSD matrices. -/
noncomputable def shiftedPaperSmallSideGramPSD
    (M : Matrix (Fin m) (Fin n) ℂ) :
    ComplexSample (m := m) (n := n) →
      {A : Matrix (Fin (min m n)) (Fin (min m n)) ℂ // A.PosSemidef} :=
  fun z => ⟨paperSmallSideGram (complexSampleMatrix z + M),
    paperSmallSideGram_posSemidef (complexSampleMatrix z + M)⟩

theorem measurable_shiftedPaperSmallSideGramPSD
    (M : Matrix (Fin m) (Fin n) ℂ) :
    Measurable (shiftedPaperSmallSideGramPSD M) := by
  unfold shiftedPaperSmallSideGramPSD
  exact (measurable_shiftedPaperSmallSideGram M).subtype_mk
    (h := fun z => paperSmallSideGram_posSemidef (complexSampleMatrix z + M))

end JinWishart
