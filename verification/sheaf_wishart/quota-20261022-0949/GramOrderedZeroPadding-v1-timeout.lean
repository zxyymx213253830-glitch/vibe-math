import JinWishartFormalization.HermitianSpectralOrbit
import JinWishartFormalization.GramSpectrumTransfer
import Mathlib.Data.Multiset.Sort

/-! Codex. Seed2026102601 controls precede source. Descending Gram lists keep
all multiplicities, including rank deficiency. Zero padding belongs at the end.
[需人工审查] Sorted-index and paper small-side conventions. -/
open Matrix Polynomial
namespace JinWishart
noncomputable section

theorem hermitian_ordered_zero_padding {a b d : ℕ}
    {A : Matrix (Fin a) (Fin a) ℂ} {B : Matrix (Fin b) (Fin b) ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hpos : ∀ i, 0 ≤ hA.eigenvalues₀ i)
    (hpoly : B.charpoly = X^d * A.charpoly) :
    List.ofFn hB.eigenvalues₀ = List.ofFn hA.eigenvalues₀ ++ List.replicate d 0 := by
  classical
  have hroots : B.charpoly.roots.map Complex.re =
      (List.ofFn hA.eigenvalues₀ ++ List.replicate d (0 : ℝ) : List ℝ) := by
    rw [hpoly, Polynomial.roots_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero)
      (Matrix.charpoly_monic A).ne_zero), Polynomial.roots_X_pow]
    have ha : A.charpoly.roots.map Complex.re = (List.ofFn hA.eigenvalues₀ : Multiset ℝ) := by
      rw [← hA.sort_roots_charpoly_eq_eigenvalues₀, Multiset.sort_eq]
    simp only [Multiset.map_add, Multiset.map_nsmul, Multiset.map_singleton,
      Complex.zero_re, ha, Multiset.nsmul_singleton, ← Multiset.coe_replicate]
    simp only [Multiset.coe_add]
    exact add_comm _ _
  have hs : (List.ofFn hA.eigenvalues₀ ++ List.replicate d (0 : ℝ)).SortedGE := by
    apply List.sortedGE_append.mpr
    refine ⟨hA.eigenvalues₀_antitone.sortedGE_ofFn, ?_, ?_⟩
    · exact List.pairwise_replicate.mpr (by simp)
    · intro x hx y hy
      have hy0 : y = 0 := List.eq_of_mem_replicate hy
      subst y
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact hpos i
  rw [← hB.sort_roots_charpoly_eq_eigenvalues₀, hroots, Multiset.coe_sort]
  exact List.mergeSort_eq_self hs.pairwise

theorem gram_ordered_column_eq_row_append_zeros {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (hmn : m ≤ n) :
    List.ofFn (complexGram_posSemidef A).1.eigenvalues₀ =
      List.ofFn (complexGram_posSemidef Aᴴ).1.eigenvalues₀ ++ List.replicate (n-m) 0 := by
  apply hermitian_ordered_zero_padding
  · exact complexGram_eigenvalues₀_nonneg Aᴴ
  · simpa only [complexGram, Matrix.conjTranspose_conjTranspose] using
      charpoly_rowGram_eq_X_pow_mul_charpoly_colGram Aᴴ hmn

theorem gram_ordered_row_column_prefix {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (hmn : m ≤ n) (i : Fin m) :
    (complexGram_posSemidef Aᴴ).1.eigenvalues₀
      (Fin.cast (Fintype.card_fin m).symm i) =
    (complexGram_posSemidef A).1.eigenvalues₀
      (Fin.cast (Fintype.card_fin n).symm (Fin.castLE hmn i)) := by
  have h := gram_ordered_column_eq_row_append_zeros A hmn
  have hi : i.val < (List.ofFn (complexGram_posSemidef Aᴴ).1.eigenvalues₀).length := by
    simpa using i.isLt
  have hn : i.val < (List.ofFn (complexGram_posSemidef A).1.eigenvalues₀).length := by
    simp only [List.length_ofFn, Fintype.card_fin]
    omega
  have he := congrArg (fun l : List ℝ => l[i.val]?) h
  rw [List.getElem?_eq_getElem hn, List.getElem?_append_left hi,
    List.getElem?_eq_getElem hi] at he
  simpa only [List.getElem_ofFn, Option.some.injEq] using he.symm

end
end JinWishart
#print axioms JinWishart.hermitian_ordered_zero_padding
#print axioms JinWishart.gram_ordered_column_eq_row_append_zeros
#print axioms JinWishart.gram_ordered_row_column_prefix
