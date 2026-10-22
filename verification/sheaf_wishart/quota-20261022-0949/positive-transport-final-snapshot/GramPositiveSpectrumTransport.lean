import JinWishartFormalization.GramSpectrumTransfer
import JinWishartFormalization.FixedRankPositiveMinimum

/-! Positive Gram-spectrum members and minima transport across different column
sizes when row Gram agrees. Codex deterministic proofs, includes empty sizes.
No zero-root equality or inverse-moment claim. -/
open Matrix
namespace JinWishart
noncomputable section

theorem hermitian_real_root_iff_ordered_eigenvalue {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (x : ℝ) :
    (x : ℂ) ∈ A.charpoly.roots ↔
      ∃ i : Fin (Fintype.card (Fin n)),hA.eigenvalues₀ i=x := by
  classical
  rw [hA.roots_charpoly_eq_eigenvalues₀]
  constructor
  · intro h
    obtain ⟨i,_,hi⟩ := Multiset.mem_map.mp h
    refine ⟨i,?_⟩
    change (hA.eigenvalues₀ i : ℂ)=(x : ℂ) at hi
    exact_mod_cast hi
  · rintro ⟨i,hi⟩
    refine Multiset.mem_map.mpr ⟨i,by simp,?_⟩
    change (hA.eigenvalues₀ i : ℂ)=(x : ℂ)
    exact congrArg (fun y : ℝ => (y : ℂ)) hi

theorem gram_nonzero_root_mem_iff_conjTranspose {m n : ℕ}
    (X : Matrix (Fin m) (Fin n) ℂ) (z : ℂ) (hz : z≠0) :
    z ∈ (complexGram X).charpoly.roots ↔ z ∈ (complexGram Xᴴ).charpoly.roots := by
  classical
  have hc : ((complexGram X).charpoly.roots).count z=
      ((complexGram Xᴴ).charpoly.roots).count z := by
    by_cases hnm : n≤m
    · have h := roots_count_eq_of_ne_zero X hnm hz
      simpa only [complexGram,Matrix.conjTranspose_conjTranspose] using h.symm
    · have hmn : m≤n := by omega
      have h := roots_count_eq_of_ne_zero Xᴴ hmn hz
      simpa only [complexGram,Matrix.conjTranspose_conjTranspose] using h
  rw [← Multiset.count_pos,← Multiset.count_pos,hc]

theorem gram_positive_eigenvalue_mem_iff_of_rowGram_eq {m n q : ℕ}
    (X : Matrix (Fin m) (Fin n) ℂ) (Y : Matrix (Fin m) (Fin q) ℂ)
    (hrow : X*Xᴴ=Y*Yᴴ) (x : ℝ) (hx : 0<x) :
    (∃ i : Fin (Fintype.card (Fin n)),(complexGram_posSemidef X).1.eigenvalues₀ i=x) ↔
      ∃ j : Fin (Fintype.card (Fin q)),(complexGram_posSemidef Y).1.eigenvalues₀ j=x := by
  have hxC : (x : ℂ)≠0 := by exact_mod_cast hx.ne'
  have hrow' : complexGram Xᴴ=complexGram Yᴴ := by
    simpa only [complexGram,Matrix.conjTranspose_conjTranspose] using hrow
  calc
    _ ↔ (x : ℂ) ∈ (complexGram X).charpoly.roots :=
      (hermitian_real_root_iff_ordered_eigenvalue _ (complexGram_posSemidef X).1 x).symm
    _ ↔ (x : ℂ) ∈ (complexGram Xᴴ).charpoly.roots :=
      gram_nonzero_root_mem_iff_conjTranspose X _ hxC
    _ ↔ (x : ℂ) ∈ (complexGram Yᴴ).charpoly.roots := by rw [hrow']
    _ ↔ (x : ℂ) ∈ (complexGram Y).charpoly.roots :=
      (gram_nonzero_root_mem_iff_conjTranspose Y _ hxC).symm
    _ ↔ _ := hermitian_real_root_iff_ordered_eigenvalue _ (complexGram_posSemidef Y).1 x

theorem gram_min_positive_eq_of_rowGram_eq {m n q : ℕ}
    (X : Matrix (Fin m) (Fin n) ℂ) (Y : Matrix (Fin m) (Fin q) ℂ)
    (hrow : X*Xᴴ=Y*Yᴴ)
    (i : Fin (Fintype.card (Fin n))) (j : Fin (Fintype.card (Fin q)))
    (hi : 0<(complexGram_posSemidef X).1.eigenvalues₀ i)
    (hj : 0<(complexGram_posSemidef Y).1.eigenvalues₀ j)
    (hminX : ∀ k,0<(complexGram_posSemidef X).1.eigenvalues₀ k →
      (complexGram_posSemidef X).1.eigenvalues₀ i≤(complexGram_posSemidef X).1.eigenvalues₀ k)
    (hminY : ∀ k,0<(complexGram_posSemidef Y).1.eigenvalues₀ k →
      (complexGram_posSemidef Y).1.eigenvalues₀ j≤(complexGram_posSemidef Y).1.eigenvalues₀ k) :
    (complexGram_posSemidef X).1.eigenvalues₀ i=(complexGram_posSemidef Y).1.eigenvalues₀ j := by
  apply le_antisymm
  · obtain ⟨k,hk⟩ := (gram_positive_eigenvalue_mem_iff_of_rowGram_eq X Y hrow _ hj).mpr ⟨j,rfl⟩
    have h := hminX k (by rw [hk];exact hj)
    simpa only [hk] using h
  · obtain ⟨k,hk⟩ := (gram_positive_eigenvalue_mem_iff_of_rowGram_eq X Y hrow _ hi).mp ⟨i,rfl⟩
    have h := hminY k (by rw [hk];exact hi)
    simpa only [hk] using h

end
end JinWishart
#print axioms JinWishart.hermitian_real_root_iff_ordered_eigenvalue
#print axioms JinWishart.gram_nonzero_root_mem_iff_conjTranspose
#print axioms JinWishart.gram_positive_eigenvalue_mem_iff_of_rowGram_eq
#print axioms JinWishart.gram_min_positive_eq_of_rowGram_eq
