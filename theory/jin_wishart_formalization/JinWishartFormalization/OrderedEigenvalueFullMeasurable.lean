import JinWishartFormalization.OrderedEigenvalueMeasurable

/-!
# Full ordered-spectrum measurability: the remaining continuity interface

Mathlib supplies the descending eigenvalue coordinates and their antitonicity,
but the pinned matrix-spectrum API does not expose continuity/measurability of
each indexed coordinate as a function of a Hermitian matrix. This file isolates
that single missing matrix-level fact and proves that it suffices for the full
actual shifted-Gram eigenvalue vector to be measurable.
-/

open MeasureTheory Matrix

namespace JinWishart

/-- Finite complex Hermitian matrices of size `n`, represented as a subtype. -/
abbrev HermitianMatrix (n : ℕ) :=
  {A : Matrix (Fin n) (Fin n) ℂ // A.IsHermitian}

/-- The full descending real eigenvalue vector of a Hermitian matrix. -/
noncomputable def hermitianEigenvalueVector {n : ℕ} (A : HermitianMatrix n) :
    Fin (Fintype.card (Fin n)) → ℝ :=
  A.2.eigenvalues₀

/-- If each indexed eigenvalue coordinate is continuous on the Hermitian matrix
space, then the whole finite ordered eigenvalue vector is measurable. -/
theorem measurable_hermitianEigenvalueVector_of_continuous
    {n : ℕ}
    (hcont : ∀ i : Fin (Fintype.card (Fin n)),
      Continuous (fun A : HermitianMatrix n => hermitianEigenvalueVector A i)) :
    Measurable (hermitianEigenvalueVector (n := n)) := by
  rw [measurable_pi_iff]
  intro i
  exact (hcont i).measurable

/-- The shifted Gram sample viewed as a measurable map into the subtype of
Hermitian matrices. -/
noncomputable def shiftedComplexGramHermitian
    {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) :
    ComplexSample (m := m) (n := n) → HermitianMatrix n :=
  fun z =>
    ⟨complexGram (complexSampleMatrix z + M),
      (complexGram_posSemidef (complexSampleMatrix z + M)).1⟩

theorem measurable_shiftedComplexGramHermitian
    {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) :
    Measurable (shiftedComplexGramHermitian M) := by
  unfold shiftedComplexGramHermitian
  exact (measurable_shiftedComplexSampleGram M).subtype_mk
    (h := fun z => (complexGram_posSemidef (complexSampleMatrix z + M)).1)

/-- Under the single matrix-level continuity premise, the complete indexed
ordered eigenvalue vector of the actual shifted complex Gram sample is
measurable. This theorem handles all indices, not just the spectral endpoints. -/
theorem measurable_complexNoncentralSampleEigenvalueVector_of_continuous
    {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ)
    (hcont : ∀ i : Fin (Fintype.card (Fin n)),
      Continuous (fun A : HermitianMatrix n => hermitianEigenvalueVector A i)) :
    Measurable (fun z : ComplexSample (m := m) (n := n) =>
      fun i => complexNoncentralSampleEigenvalue M i z) := by
  rw [measurable_pi_iff]
  intro i
  change Measurable
    ((fun A : HermitianMatrix n => hermitianEigenvalueVector A i) ∘
      shiftedComplexGramHermitian M)
  exact (hcont i).measurable.comp (measurable_shiftedComplexGramHermitian M)

/-- The exact missing continuity lemma sufficient to close general indexed
ordered-spectrum measurability in this model. -/
def OrderedHermitianEigenvalueCoordinatesContinuous (n : ℕ) : Prop :=
  ∀ i : Fin (Fintype.card (Fin n)),
    Continuous (fun A : HermitianMatrix n => hermitianEigenvalueVector A i)

end JinWishart
