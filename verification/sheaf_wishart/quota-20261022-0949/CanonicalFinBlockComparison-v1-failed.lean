import JinWishartFormalization.CanonicalFinShear

/-! Deterministic canonical D/E positive-minimum comparison with explicit shear factor.
No Gaussian integration or inverse-moment threshold is asserted.
[需人工审查] Subsequent actual-model AE and moment transport. -/
open Matrix
open scoped ComplexOrder
namespace JinWishart
noncomputable section

private theorem control_adjoint {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ) :
    matrixColumnControl Sᴴ=matrixColumnControl S := by
  unfold matrixColumnControl
  rw [← Matrix.star_eq_conjTranspose, map_star, norm_star]

theorem canonical_fin_shear_positive_bounds {m n b c : ℕ}
    (D : Matrix (Fin m) (Fin n) ℂ) (e : (Fin b ⊕ Fin c) ≃ Fin n)
    (K : Matrix (Fin c) (Fin b) ℂ) (hm : 0<m) (hn : 0<n)
    (hr : D.rank=min m n) (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=min m n) :
    let E := D*canonicalFinShear e (-K)
    let L := (1+‖(Matrix.toEuclideanLin K).toContinuousLinearMap‖)^2
    0<(complexGram_posSemidef D).1.eigenvalues₀ i ∧
    0<(complexGram_posSemidef E).1.eigenvalues₀ i ∧
    (complexGram_posSemidef E).1.eigenvalues₀ i ≤ L*(complexGram_posSemidef D).1.eigenvalues₀ i ∧
    (complexGram_posSemidef D).1.eigenvalues₀ i ≤ L*(complexGram_posSemidef E).1.eigenvalues₀ i := by
  dsimp only
  let S := canonicalFinShear e (-K)
  have hS : IsUnit S.det := Matrix.isUnit_det_of_left_inverse (canonical_fin_shear_inverse e K).2.1
  obtain ⟨hC,hI⟩ := canonical_fin_shear_control_le e K
  by_cases hnm : n≤m
  · have he := Nat.min_eq_right hnm
    obtain ⟨hD,hE,hu,hl⟩ := full_column_rank_positive_coordinate_mul_bounds D S hn hS
      (hr.trans he) i (hi.trans he)
    exact ⟨hD,hE,hu.trans (mul_le_mul_of_nonneg_right hC hD.le),
      hl.trans (mul_le_mul_of_nonneg_right hI hE.le)⟩
  · have he : min m n=m := Nat.min_eq_left (by omega)
    obtain ⟨hD,hE,hu,hl⟩ := full_row_rank_positive_coordinate_mul_bounds D S hm hS
      (hr.trans he) i (hi.trans he)
    rw [control_adjoint] at hu
    rw [← Matrix.conjTranspose_nonsing_inv,control_adjoint] at hl
    exact ⟨hD,hE,hu.trans (mul_le_mul_of_nonneg_right hC hD.le),
      hl.trans (mul_le_mul_of_nonneg_right hI hE.le)⟩

def canonicalFinBlock {a b c m n : ℕ}
    (er : (Fin a ⊕ Fin c) ≃ Fin m) (ec : (Fin b ⊕ Fin c) ≃ Fin n)
    (A : Matrix (Fin a) (Fin b) ℂ) (H : Matrix (Fin c) (Fin b) ℂ)
    (N : Matrix (Fin c) (Fin c) ℂ) : Matrix (Fin m) (Fin n) ℂ :=
  Matrix.reindexLinearEquiv ℂ ℂ er ec (fromBlocks A 0 H N)

theorem canonical_fin_diagonal_gram_charpoly {a b c m n : ℕ}
    (er : (Fin a ⊕ Fin c) ≃ Fin m) (ec : (Fin b ⊕ Fin c) ≃ Fin n)
    (A : Matrix (Fin a) (Fin b) ℂ) (N : Matrix (Fin c) (Fin c) ℂ) :
    ((canonicalFinBlock er ec A 0 N)ᴴ*canonicalFinBlock er ec A 0 N).charpoly=
      (Aᴴ*A).charpoly*(Nᴴ*N).charpoly := by
  unfold canonicalFinBlock
  change ((Matrix.reindex er ec (fromBlocks A 0 0 N))ᴴ*
    Matrix.reindex er ec (fromBlocks A 0 0 N)).charpoly=_
  rw [Matrix.conjTranspose_reindex]
  change ((Matrix.reindexLinearEquiv ℂ ℂ ec er (fromBlocks A 0 0 N)ᴴ)*
    (Matrix.reindexLinearEquiv ℂ ℂ er ec (fromBlocks A 0 0 N))).charpoly=_
  rw [Matrix.reindexLinearEquiv_mul]
  exact (Matrix.charpoly_reindex ec _).trans (canonical_block_gram_charpoly A N)

private theorem realRoot {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℂ) (hG : G.IsHermitian) (x : ℝ) :
    (x : ℂ) ∈ G.charpoly.roots ↔ ∃ i, hG.eigenvalues₀ i=x := by
  classical
  rw [hG.roots_charpoly_eq_eigenvalues₀]
  constructor
  · intro h
    obtain ⟨i,_,hi⟩ := Multiset.mem_map.mp h
    exact ⟨i,by exact_mod_cast hi⟩
  · rintro ⟨i,hi⟩
    exact Multiset.mem_map.mpr ⟨i,by simp,congrArg (fun y : ℝ => (y : ℂ)) hi⟩

theorem canonical_fin_block_minimum_bounds {a b c m n : ℕ}
    (er : (Fin a ⊕ Fin c) ≃ Fin m) (ec : (Fin b ⊕ Fin c) ≃ Fin n)
    (A : Matrix (Fin a) (Fin b) ℂ) (H K : Matrix (Fin c) (Fin b) ℂ)
    (N : Matrix (Fin c) (Fin c) ℂ) (hK : N*K=H)
    (hm : 0<m) (hn : 0<n) (hr : (canonicalFinBlock er ec A H N).rank=min m n)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=min m n)
    (j : Fin (Fintype.card (Fin b))) (k : Fin (Fintype.card (Fin c)))
    (hj : 0<(complexGram_posSemidef A).1.eigenvalues₀ j)
    (hk : 0<(complexGram_posSemidef N).1.eigenvalues₀ k)
    (hminA : ∀ l,0<(complexGram_posSemidef A).1.eigenvalues₀ l →
      (complexGram_posSemidef A).1.eigenvalues₀ j≤(complexGram_posSemidef A).1.eigenvalues₀ l)
    (hminN : ∀ l,0<(complexGram_posSemidef N).1.eigenvalues₀ l →
      (complexGram_posSemidef N).1.eigenvalues₀ k≤(complexGram_posSemidef N).1.eigenvalues₀ l) :
    let D := canonicalFinBlock er ec A H N
    let q := min ((complexGram_posSemidef A).1.eigenvalues₀ j)
      ((complexGram_posSemidef N).1.eigenvalues₀ k)
    let L := (1+‖(Matrix.toEuclideanLin K).toContinuousLinearMap‖)^2
    0<(complexGram_posSemidef D).1.eigenvalues₀ i ∧ 0<q ∧
    q≤L*(complexGram_posSemidef D).1.eigenvalues₀ i ∧
    (complexGram_posSemidef D).1.eigenvalues₀ i≤L*q := by
  classical
  dsimp only
  let D := canonicalFinBlock er ec A H N
  let E := canonicalFinBlock er ec A 0 N
  have hDE : D*canonicalFinShear ec (-K)=E := by
    unfold D E canonicalFinBlock canonicalFinShear
    rw [Matrix.reindexLinearEquiv_mul,canonical_block_shear_cancel A H K N hK]
  obtain ⟨hD,hE,hu,hl⟩ := canonical_fin_shear_positive_bounds D ec K hm hn hr i hi
  dsimp only at hD hE hu hl
  rw [hDE] at hE hu hl
  have hrE : E.rank=min m n := by
    rw [← hDE,Matrix.rank_mul_eq_left_of_isUnit_det _ _
      (Matrix.isUnit_det_of_left_inverse (canonical_fin_shear_inverse ec K).2.1)]
    exact hr
  have hminE := (antitone_min_positive_at_count _ (complexGram_posSemidef E).1.eigenvalues₀_antitone
    i ((gram_positive_modes_card_eq_rank E).trans (hrE.trans hi.symm))).2
  have hmem (x : ℝ) :
      (∃ l,(complexGram_posSemidef E).1.eigenvalues₀ l=x) ↔
      (∃ l,(complexGram_posSemidef A).1.eigenvalues₀ l=x) ∨
      (∃ l,(complexGram_posSemidef N).1.eigenvalues₀ l=x) := by
    rw [← realRoot _ (complexGram_posSemidef E).1 x]
    change (x : ℂ) ∈ ((canonicalFinBlock er ec A 0 N)ᴴ*canonicalFinBlock er ec A 0 N).charpoly.roots ↔ _
    rw [canonical_fin_diagonal_gram_charpoly,Polynomial.roots_mul
      (mul_ne_zero (Matrix.charpoly_monic _).ne_zero (Matrix.charpoly_monic _).ne_zero),Multiset.mem_add,
      realRoot _ (complexGram_posSemidef A).1 x,realRoot _ (complexGram_posSemidef N).1 x]
  have heq : (complexGram_posSemidef E).1.eigenvalues₀ i=
      min ((complexGram_posSemidef A).1.eigenvalues₀ j) ((complexGram_posSemidef N).1.eigenvalues₀ k) := by
    apply le_antisymm
    · apply le_min
      · obtain ⟨l,he⟩ := (hmem _).mpr (Or.inl ⟨j,rfl⟩)
        simpa only [he] using hminE l (by rw [he];exact hj)
      · obtain ⟨l,he⟩ := (hmem _).mpr (Or.inr ⟨k,rfl⟩)
        simpa only [he] using hminE l (by rw [he];exact hk)
    · obtain ha|hn := (hmem _).mp ⟨i,rfl⟩
      · obtain ⟨l,he⟩ := ha
        exact (min_le_left _ _).trans (by simpa only [he] using hminA l (by rw [he];exact hE))
      · obtain ⟨l,he⟩ := hn
        exact (min_le_right _ _).trans (by simpa only [he] using hminN l (by rw [he];exact hE))
  rw [heq] at hE hu hl
  exact ⟨hD,hE,hu,hl⟩

end
end JinWishart
#print axioms JinWishart.canonical_fin_shear_positive_bounds
#print axioms JinWishart.canonical_fin_diagonal_gram_charpoly
#print axioms JinWishart.canonical_fin_block_minimum_bounds
