import JinWishartFormalization.PaperNoncentralSpectralOrbitLaw
import JinWishartFormalization.FixedRankPositiveMinimum

/-! Codex. Seed2026102602 pre-source exact controls. The positive mean spectrum
has length rank(M), not the random sample rank. Positive repetitions are allowed.
Original-paper strictness is an explicit additional hypothesis.
[需人工审查] Source-paper noncentrality and covariance conventions. -/
open Matrix MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

def meanPositiveNoncentrality {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ)
    (i : Fin M.rank) : ℝ :=
  (complexGram_posSemidef M).1.eigenvalues₀
    (Fin.cast (Fintype.card_fin n).symm (Fin.castLE (Matrix.rank_le_width M) i))

theorem meanPositiveNoncentrality_pos {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (i : Fin M.rank) :
    0 < meanPositiveNoncentrality M i := by
  unfold meanPositiveNoncentrality
  apply (antitone_positive_iff_lt_count _
    (complexGram_posSemidef M).1.eigenvalues₀_antitone _).mpr
  rw [gram_positive_modes_card_eq_rank]
  exact i.isLt

theorem meanPositiveNoncentrality_antitone {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) : Antitone (meanPositiveNoncentrality M) := by
  intro i j hij
  apply (complexGram_posSemidef M).1.eigenvalues₀_antitone
  exact hij

theorem meanGram_eigenvalue_zero_iff_rank_le_index {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (i : Fin (Fintype.card (Fin n))) :
    (complexGram_posSemidef M).1.eigenvalues₀ i = 0 ↔ M.rank ≤ i.val := by
  have hp := antitone_positive_iff_lt_count _
    (complexGram_posSemidef M).1.eigenvalues₀_antitone i
  rw [gram_positive_modes_card_eq_rank] at hp
  have hn := complexGram_eigenvalues₀_nonneg M i
  constructor
  · intro hz
    by_contra h
    have ht := hp.mpr (lt_of_not_ge h)
    rw [hz] at ht
    exact (lt_irrefl (0 : ℝ)) ht
  · intro hi
    apply le_antisymm _ hn
    exact le_of_not_gt (fun h => (not_lt_of_ge hi) (hp.mp h))

theorem meanGram_eigenvalue_positive_parameter_or_zero {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (i : Fin (Fintype.card (Fin n))) :
    (complexGram_posSemidef M).1.eigenvalues₀ i =
      if h : i.val < M.rank then meanPositiveNoncentrality M ⟨i.val,h⟩ else 0 := by
  by_cases hi : i.val < M.rank
  · rw [dif_pos hi]
    unfold meanPositiveNoncentrality
    congr 1
  · rw [dif_neg hi]
    exact (meanGram_eigenvalue_zero_iff_rank_le_index M i).mpr (le_of_not_gt hi)

theorem exists_paper_positiveNoncentralSpectrum_of_strict {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (hs : StrictAnti (meanPositiveNoncentrality M)) :
    ∃ p : OrderedPositiveNoncentralSpectrum M.rank,
      p.values = meanPositiveNoncentrality M := by
  exact ⟨⟨meanPositiveNoncentrality M, meanPositiveNoncentrality_pos M, hs⟩, rfl⟩

theorem actualNoncentral_paperJointSpectrum_law_of_positive_parameters {m n : ℕ}
    (M N : Matrix (Fin m) (Fin n) ℂ) (hRank : M.rank = N.rank)
    (hParams : ∀ i : Fin M.rank,
      meanPositiveNoncentrality M i = meanPositiveNoncentrality N (Fin.cast hRank i)) :
    (stdGaussian (ComplexSample (m := m) (n := n))).map (paperJointSpectrum M) =
      (stdGaussian (ComplexSample (m := m) (n := n))).map (paperJointSpectrum N) := by
  apply actualNoncentral_paperJointSpectrum_law_of_meanGram_eigenvalues
  change (complexGram_posSemidef M).1.eigenvalues₀ = (complexGram_posSemidef N).1.eigenvalues₀
  funext i
  rw [meanGram_eigenvalue_positive_parameter_or_zero M i,
    meanGram_eigenvalue_positive_parameter_or_zero N i]
  by_cases hm : i.val < M.rank
  · have hn : i.val < N.rank := by omega
    rw [dif_pos hm, dif_pos hn]
    convert hParams ⟨i.val,hm⟩ using 1 <;> congr 1
  · have hn : ¬ i.val < N.rank := by omega
    rw [dif_neg hm, dif_neg hn]

end
end JinWishart
#print axioms JinWishart.meanPositiveNoncentrality_pos
#print axioms JinWishart.meanPositiveNoncentrality_antitone
#print axioms JinWishart.meanGram_eigenvalue_zero_iff_rank_le_index
#print axioms JinWishart.meanGram_eigenvalue_positive_parameter_or_zero
#print axioms JinWishart.exists_paper_positiveNoncentralSpectrum_of_strict
#print axioms JinWishart.actualNoncentral_paperJointSpectrum_law_of_positive_parameters
