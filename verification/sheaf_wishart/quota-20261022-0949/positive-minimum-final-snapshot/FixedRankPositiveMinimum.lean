import JinWishartFormalization.FinitePositiveMinimum
import JinWishartFormalization.CorrelatedLogDetGenericRank

/-! A fixed measurable ordered coordinate is AE the smallest strictly positive
Gram eigenvalue at positive deterministic generic rank. Codex.
[需人工审查] Inherited AE rank, spectrum/law and physical-model transport.
No inverse-moment threshold or all-sample positive-minimum selector claimed. -/
open Matrix MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

theorem gram_positive_modes_card_eq_rank {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℂ) :
    (Finset.univ.filter (fun i => 0<(complexGram_posSemidef X).1.eigenvalues₀ i)).card=X.rank := by
  classical
  have h := gram_positive_modes_eq_rank X
  rw [Finset.sum_boole] at h
  exact_mod_cast h

theorem exists_actualCorrelated_smallest_positive_coordinate {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (hR : 0<min m (Matrix.fromRows B M).rank) :
    ∃ i : Fin (Fintype.card (Fin n)),
      i.val+1=min m (Matrix.fromRows B M).rank ∧
      Measurable (actualCorrelatedEigenvalue B M i) ∧
      ∀ᵐ z ∂stdGaussian (ComplexSample (m := m) (n := p)),
        0<actualCorrelatedEigenvalue B M i z ∧
        ∀ j,0<actualCorrelatedEigenvalue B M j z →
          actualCorrelatedEigenvalue B M i z≤actualCorrelatedEigenvalue B M j z := by
  classical
  let R := min m (Matrix.fromRows B M).rank
  have hRn : R≤Fintype.card (Fin n) :=
    (min_le_right _ _).trans (Matrix.rank_le_card_width _)
  let i : Fin (Fintype.card (Fin n)) := ⟨R-1,by dsimp [R] at *;omega⟩
  have hi : i.val+1=R := by dsimp [i,R];omega
  refine ⟨i,hi,measurable_actualCorrelatedEigenvalue B M i,?_⟩
  filter_upwards [actualCorrelatedRank_eq_generic_ae B M] with z hz
  let X := complexSampleMatrix z*B+M
  have hcount : (Finset.univ.filter (fun j => 0<actualCorrelatedEigenvalue B M j z)).card=
      i.val+1 := by
    calc
      _ = X.rank := gram_positive_modes_card_eq_rank X
      _ = R := by rw [hz,← matrix_fromRows_rank_eq]
      _ = i.val+1 := hi.symm
  exact antitone_min_positive_at_count (fun j => actualCorrelatedEigenvalue B M j z)
    (complexGram_posSemidef X).1.eigenvalues₀_antitone i hcount

end
end JinWishart
#print axioms JinWishart.gram_positive_modes_card_eq_rank
#print axioms JinWishart.exists_actualCorrelated_smallest_positive_coordinate
