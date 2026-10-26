import JinWishartFormalization.GramOrderedZeroPadding
import JinWishartFormalization.ActualNoncentralSpectralOrbitLaw
import JinWishartFormalization.GaussianMatrixSpectralIntegral

/-! Codex. Seed2026102601 controls precede source. The paper's small-side ordered
vector is the initial min(m,n) segment of the full column-Gram spectrum.
[需人工审查] Source noncentrality/rank-L convention and Borel model mapping. -/
open Matrix MeasureTheory ProbabilityTheory Polynomial
namespace JinWishart
noncomputable section

private theorem psd_ordered_nonneg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (i : Fin (Fintype.card (Fin n))) : 0 ≤ hA.1.eigenvalues₀ i := by
  have h := hA.eigenvalues_nonneg ((Fintype.equivOfCardEq (Fintype.card_fin _)) i)
  simpa only [Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply] using h

theorem paperSmallSide_ordered_column_zero_padding {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) :
    List.ofFn (complexGram_posSemidef A).1.eigenvalues₀ =
      List.ofFn (paperSmallSideGram_posSemidef A).1.eigenvalues₀ ++
        List.replicate (n-min m n) 0 := by
  apply hermitian_ordered_zero_padding
  · exact psd_ordered_nonneg (paperSmallSideGram_posSemidef A)
  · by_cases hmn : m ≤ n
    · rw [paperSmallSideGram, dif_pos hmn, charpoly_submatrix_equiv]
      simpa only [complexGram, Matrix.conjTranspose_conjTranspose, Nat.min_eq_left hmn] using
        charpoly_rowGram_eq_X_pow_mul_charpoly_colGram Aᴴ hmn
    · have hnm : n ≤ m := le_of_not_ge hmn
      rw [Nat.min_eq_right hnm, Nat.sub_self, pow_zero, one_mul]
      exact (charpoly_paperSmallSideGram_eq_charpoly_colGram A hnm).symm

theorem paperSmallSide_ordered_column_prefix {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (i : Fin (min m n)) :
    (paperSmallSideGram_posSemidef A).1.eigenvalues₀
      (Fin.cast (Fintype.card_fin (min m n)).symm i) =
    (complexGram_posSemidef A).1.eigenvalues₀
      (Fin.cast (Fintype.card_fin n).symm (Fin.castLE (Nat.min_le_right m n) i)) := by
  have h := paperSmallSide_ordered_column_zero_padding A
  have hi : i.val < (List.ofFn (paperSmallSideGram_posSemidef A).1.eigenvalues₀).length := by
    simpa using i.isLt
  have hn : i.val < (List.ofFn (complexGram_posSemidef A).1.eigenvalues₀).length := by
    simp only [List.length_ofFn, Fintype.card_fin]
    exact lt_of_lt_of_le i.isLt (Nat.min_le_right m n)
  have he := congrArg (fun l : List ℝ => l[i.val]?) h
  rw [List.getElem?_eq_getElem hn, List.getElem?_append_left hi,
    List.getElem?_eq_getElem hi] at he
  simp only [List.getElem_ofFn, Option.some.injEq] at he
  convert he.symm using 1 <;> congr 1 <;> apply Fin.ext <;> rfl

theorem actualNoncentral_paperJointSpectrum_law_of_meanGram_eigenvalues {m n : ℕ}
    (M N : Matrix (Fin m) (Fin n) ℂ)
    (h : (Matrix.isHermitian_conjTranspose_mul_self M).eigenvalues₀ =
      (Matrix.isHermitian_conjTranspose_mul_self N).eigenvalues₀) :
    (stdGaussian (ComplexSample (m := m) (n := n))).map (paperJointSpectrum M) =
      (stdGaussian (ComplexSample (m := m) (n := n))).map (paperJointSpectrum N) := by
  let P : (Fin (Fintype.card (Fin n)) → ℝ) → (Fin (min m n) → ℝ) :=
    fun v i => v (Fin.cast (Fintype.card_fin n).symm (Fin.castLE (Nat.min_le_right m n) i))
  have hP : Measurable P := by fun_prop
  have hm (K : Matrix (Fin m) (Fin n) ℂ) :
      P ∘ (fun z => fun i => complexNoncentralSampleEigenvalue K i z) = paperJointSpectrum K := by
    funext z i
    exact (paperSmallSide_ordered_column_prefix (complexSampleMatrix z+K) i).symm
  have he := congrArg (fun μ : Measure (Fin (Fintype.card (Fin n)) → ℝ) => μ.map P)
    (actualNoncentral_orderedSpectrum_law_of_meanGram_eigenvalues M N h)
  have hmeas (K : Matrix (Fin m) (Fin n) ℂ) :
      Measurable (fun z => fun i => complexNoncentralSampleEigenvalue K i z) :=
    measurable_complexNoncentralSampleEigenvalueVector_of_continuous K
      (orderedHermitianEigenvalueCoordinatesContinuous n)
  rwa [Measure.map_map hP (hmeas M), Measure.map_map hP (hmeas N), hm M, hm N] at he

theorem actualNoncentral_paperJointSpectrum_law_of_smallMeanGram_eigenvalues {m n : ℕ}
    (M N : Matrix (Fin m) (Fin n) ℂ)
    (h : (paperSmallSideGram_posSemidef M).1.eigenvalues₀ =
      (paperSmallSideGram_posSemidef N).1.eigenvalues₀) :
    (stdGaussian (ComplexSample (m := m) (n := n))).map (paperJointSpectrum M) =
      (stdGaussian (ComplexSample (m := m) (n := n))).map (paperJointSpectrum N) := by
  apply actualNoncentral_paperJointSpectrum_law_of_meanGram_eigenvalues
  apply List.ofFn_inj.mp
  rw [paperSmallSide_ordered_column_zero_padding M,
    paperSmallSide_ordered_column_zero_padding N, h]

end
end JinWishart
#print axioms JinWishart.paperSmallSide_ordered_column_zero_padding
#print axioms JinWishart.paperSmallSide_ordered_column_prefix
#print axioms JinWishart.actualNoncentral_paperJointSpectrum_law_of_meanGram_eigenvalues
#print axioms JinWishart.actualNoncentral_paperJointSpectrum_law_of_smallMeanGram_eigenvalues
