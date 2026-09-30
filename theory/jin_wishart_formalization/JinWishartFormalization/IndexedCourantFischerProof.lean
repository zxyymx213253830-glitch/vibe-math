import JinWishartFormalization.OrderedCourantFischerFiniteDim
import JinWishartFormalization.SpectralCoordinateSpanSupport
import JinWishartFormalization.IndexedCourantFischerAttempt

/-!
# Indexed Courant--Fischer min-max theorem for real symmetric operators

The indexing convention is descending: `eigenvalues hn i` is the `i`th eigenvalue starting at
zero. The admissible spaces have dimension `n - i.val`, so the tail spectral span is an upper
bound witness. For the converse, every admissible space intersects the first `i+1` eigenspace
span nontrivially.
-/

namespace JinWishart

open Module Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The indexed Courant--Fischer value is the `i`th descending eigenvalue. -/
theorem indexedCourantFischerValue_eq_eigenvalue
    {n : ℕ} (T : E →L[ℝ] E) (hT : (T : E →ₗ[ℝ] E).IsSymmetric)
    (hn : Module.finrank ℝ E = n) (i : Fin n) :
    indexedCourantFischerValue T n i = hT.eigenvalues hn i := by
  classical
  let b := hT.eigenvectorBasis hn
  let head : Submodule ℝ E :=
    span ℝ ((Finset.Iic i).image b)
  let tail : Submodule ℝ E :=
    span ℝ ((Finset.Ici i).image b)
  have hheadDim : finrank ℝ head = i.val + 1 := by
    let c := Finset.Iic i
    have hlin : LinearIndependent ℝ (fun j : c => (hT.eigenvectorBasis hn).toBasis j.1) :=
      (hT.eigenvectorBasis hn).toBasis.linearIndependent.comp
        Subtype.val Subtype.val_injective
    have hrange : Set.range (fun j : c => (hT.eigenvectorBasis hn).toBasis j.1) =
        ((c.image (hT.eigenvectorBasis hn).toBasis : Finset E) : Set E) := by
      ext x
      simp [c]
    change finrank ℝ ↥(span ℝ
      ((c.image (hT.eigenvectorBasis hn).toBasis : Finset E) : Set E)) = i.val + 1
    rw [← hrange]
    have hdim := finrank_span_eq_card hlin
    rw [Fintype.card_coe, Fin.card_Iic] at hdim
    exact hdim
  have htailDim : finrank ℝ tail = n - i.val := by
    let c := Finset.Ici i
    have hlin : LinearIndependent ℝ (fun j : c => (hT.eigenvectorBasis hn).toBasis j.1) :=
      (hT.eigenvectorBasis hn).toBasis.linearIndependent.comp
        Subtype.val Subtype.val_injective
    have hrange : Set.range (fun j : c => (hT.eigenvectorBasis hn).toBasis j.1) =
        ((c.image (hT.eigenvectorBasis hn).toBasis : Finset E) : Set E) := by
      ext x
      simp [c]
    change finrank ℝ ↥(span ℝ
      ((c.image (hT.eigenvectorBasis hn).toBasis : Finset E) : Set E)) = n - i.val
    rw [← hrange]
    have hdim := finrank_span_eq_card hlin
    rw [Fintype.card_coe, Fin.card_Ici] at hdim
    exact hdim
  have hlower (U : Submodule ℝ E) (hU : finrank ℝ U = n - i.val) :
      hT.eigenvalues hn i ≤ rayleighSup T U := by
    have hdim : finrank ℝ E < finrank ℝ U + finrank ℝ head := by
      rw [hU, hheadDim, hn]
      omega
    obtain ⟨x, hx, hxU, hxHead⟩ :=
      exists_ne_zero_mem_inf_of_finrank_add_gt U head hdim
    have hRay : hT.eigenvalues hn i ≤ T.rayleighQuotient x :=
      eigenvalue_le_rayleighQuotient_of_mem_spectral_head_span T hT hn i x hx
        (by simpa [head, b, Finset.coe_image, Finset.coe_Iic, Set.Iic] using hxHead)
    exact hRay.trans (rayleighQuotient_le_rayleighSup T U ⟨x, hxU⟩ hx)
  have htailNonempty : (rayleighValues T tail).Nonempty := by
    let v := b i
    have hv : v ≠ 0 := b.orthonormal.ne_zero i
    have hmem : v ∈ tail := by
      apply Submodule.subset_span
      exact Finset.mem_image.mpr ⟨i, by simp, rfl⟩
    refine ⟨T.rayleighQuotient v, ?_⟩
    exact ⟨⟨⟨v, hmem⟩, hv⟩, rfl⟩
  have htailUpper : rayleighSup T tail ≤ hT.eigenvalues hn i := by
    unfold rayleighSup
    apply csSup_le htailNonempty
    rintro y ⟨x, rfl⟩
    exact rayleighQuotient_le_eigenvalue_of_mem_spectral_tail_span T hT hn i
      x.1.1 x.2 (by simpa [tail, b, Finset.coe_image, Finset.coe_Ici, Set.Ici] using x.1.2)
  have houterNonempty : (indexedRayleighSupSet T n i).Nonempty := by
    refine ⟨rayleighSup T tail, ?_⟩
    exact ⟨⟨tail, htailDim⟩, rfl⟩
  have houterLower : ∀ y ∈ indexedRayleighSupSet T n i,
      hT.eigenvalues hn i ≤ y := by
    rintro y ⟨U, rfl⟩
    exact hlower U.1 U.2
  have hminLower : hT.eigenvalues hn i ≤ indexedCourantFischerValue T n i := by
    rw [indexedCourantFischerValue]
    exact le_csInf houterNonempty houterLower
  have htailMem : rayleighSup T tail ∈ indexedRayleighSupSet T n i :=
    ⟨⟨tail, htailDim⟩, rfl⟩
  have hminUpper : indexedCourantFischerValue T n i ≤ hT.eigenvalues hn i := by
    rw [indexedCourantFischerValue]
    have hbelow : BddBelow (indexedRayleighSupSet T n i) := ⟨hT.eigenvalues hn i, houterLower⟩
    exact (csInf_le hbelow htailMem).trans htailUpper
  exact le_antisymm hminUpper hminLower

end JinWishart
