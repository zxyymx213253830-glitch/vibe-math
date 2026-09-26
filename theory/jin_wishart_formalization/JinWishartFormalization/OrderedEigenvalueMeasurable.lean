import JinWishartFormalization.WishartProbability

/-!
# Measurability of ordered noncentral Gram eigenvalues

This file records the coordinate random variables and the endpoint cases that
follow from the measurable Loewner-order events. The general interior-coordinate
case requires a separate continuity or min-max theorem for ordered Hermitian
eigenvalues.
-/

open MeasureTheory Matrix

namespace JinWishart

variable {m n : ℕ}

/-- The `i`th descending eigenvalue of a shifted complex Gram sample. -/
noncomputable def complexNoncentralSampleEigenvalue
    (M : Matrix (Fin m) (Fin n) ℂ)
    (i : Fin (Fintype.card (Fin n)))
    (z : ComplexSample (m := m) (n := n)) : ℝ :=
  (complexGram_posSemidef (complexSampleMatrix z + M)).1.eigenvalues₀ i

theorem complexNoncentralSampleEigenvalue_antitone
    (M : Matrix (Fin m) (Fin n) ℂ)
    (z : ComplexSample (m := m) (n := n)) :
    Antitone (complexNoncentralSampleEigenvalue M · z) :=
  complexGram_eigenvalues₀_antitone (complexSampleMatrix z + M)

theorem complexNoncentralSampleEigenvalue_nonneg
    (M : Matrix (Fin m) (Fin n) ℂ)
    (i : Fin (Fintype.card (Fin n)))
    (z : ComplexSample (m := m) (n := n)) :
    0 ≤ complexNoncentralSampleEigenvalue M i z :=
  complexNoncentralGram_eigenvalues₀_nonneg M z i

theorem measurable_complexNoncentralSampleLargestEigenvalue
    (M : Matrix (Fin m) (Fin n) ℂ) (hn : 0 < n) :
    Measurable (complexNoncentralSampleEigenvalue M
      (⟨0, by simpa using hn⟩ : Fin (Fintype.card (Fin n)))) := by
  apply measurable_of_Iic
  intro x
  have hpre :
      (complexNoncentralSampleEigenvalue M
        (⟨0, by simpa using hn⟩ : Fin (Fintype.card (Fin n)))) ⁻¹' Set.Iic x =
        (fun z : ComplexSample (m := m) (n := n) =>
          complexGram (complexSampleMatrix z + M)) ⁻¹'
          largestEigenvalueCdfEvent x := by
    ext z
    exact (largestEigenvalueCdfEvent_iff_largest_eigenvalue₀_le
      (complexGram (complexSampleMatrix z + M))
      (complexGram_posSemidef (complexSampleMatrix z + M)).1
      (by simpa using hn) x).symm
  rw [hpre]
  exact (measurableSet_largestEigenvalueCdfEvent x).preimage
    (measurable_shiftedComplexSampleGram M)

theorem measurable_complexNoncentralSampleEigenvalue_last
    (M : Matrix (Fin m) (Fin n) ℂ) (hn : 0 < n) :
    Measurable (complexNoncentralSampleEigenvalue M (smallestEigenvalue₀Index hn)) := by
  exact measurable_complexNoncentralSampleSmallestEigenvalue M hn

end JinWishart
