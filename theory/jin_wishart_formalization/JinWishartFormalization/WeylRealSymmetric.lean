import JinWishartFormalization.SpectralCoordinateSpanSupport
import JinWishartFormalization.SubspaceIntersectionFinrank
import JinWishartFormalization.OrderedEigenvalueWeyl
import JinWishartFormalization.IndexedCourantFischerAttempt

/-!
# Weyl's perturbation bound for ordered eigenvalues of real symmetric operators

This proof uses spectral head/tail spans, the finite-dimensional intersection lemma, and the
Rayleigh quotient perturbation bound. Eigenvalues are indexed in Mathlib's descending order.
-/

namespace JinWishart

open Module Submodule

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem finrank_spectralHeadSpan
    {n : ℕ} [DecidableEq E] (T : E →L[ℝ] E) (hT : (T : E →ₗ[ℝ] E).IsSymmetric)
    (hn : finrank ℝ E = n) (i : Fin n) :
    finrank ℝ (span ℝ (((Finset.Iic i).image (hT.eigenvectorBasis hn).toBasis : Finset E) : Set E))
      = i.val + 1 := by
  classical
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

private theorem finrank_spectralTailSpan
    {n : ℕ} [DecidableEq E] (T : E →L[ℝ] E) (hT : (T : E →ₗ[ℝ] E).IsSymmetric)
    (hn : finrank ℝ E = n) (i : Fin n) :
    finrank ℝ (span ℝ (((Finset.Ici i).image (hT.eigenvectorBasis hn).toBasis : Finset E) : Set E))
      = n - i.val := by
  classical
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

/-- For two real symmetric operators on the same finite-dimensional inner-product space, each
ordered eigenvalue changes by at most the operator norm of their difference. -/
theorem abs_eigenvalue_sub_le_operatorNorm
    {n : ℕ} (T S : E →L[ℝ] E)
    (hT : (T : E →ₗ[ℝ] E).IsSymmetric)
    (hS : (S : E →ₗ[ℝ] E).IsSymmetric)
    (hn : finrank ℝ E = n) (i : Fin n) :
    |hT.eigenvalues hn i - hS.eigenvalues hn i| ≤ ‖T - S‖ := by
  classical
  let HT : Submodule ℝ E := span ℝ ((Finset.Iic i).image (hT.eigenvectorBasis hn).toBasis)
  let KS : Submodule ℝ E := span ℝ ((Finset.Ici i).image (hS.eigenvectorBasis hn).toBasis)
  let HS : Submodule ℝ E := span ℝ ((Finset.Iic i).image (hS.eigenvectorBasis hn).toBasis)
  let KT : Submodule ℝ E := span ℝ ((Finset.Ici i).image (hT.eigenvectorBasis hn).toBasis)
  have hdimHT : finrank ℝ HT = i.val + 1 := by
    simpa [HT] using finrank_spectralHeadSpan T hT hn i
  have hdimKS : finrank ℝ KS = n - i.val := by
    simpa [KS] using finrank_spectralTailSpan S hS hn i
  have hdimHS : finrank ℝ HS = i.val + 1 := by
    simpa [HS] using finrank_spectralHeadSpan S hS hn i
  have hdimKT : finrank ℝ KT = n - i.val := by
    simpa [KT] using finrank_spectralTailSpan T hT hn i
  have hsumTS : finrank ℝ E < finrank ℝ HT + finrank ℝ KS := by
    rw [hdimHT, hdimKS, hn]
    omega
  obtain ⟨x, hx, hxHT, hxKS⟩ :=
    exists_ne_zero_mem_inf_of_finrank_add_gt HT KS hsumTS
  have hprefixT : hT.eigenvalues hn i ≤ T.rayleighQuotient x :=
    eigenvalue_le_rayleighQuotient_of_mem_spectral_head_span T hT hn i x hx
      (by simpa [HT, Finset.coe_image, Finset.coe_Iic, Set.Iic] using hxHT)
  have htailS : S.rayleighQuotient x ≤ hS.eigenvalues hn i :=
    rayleighQuotient_le_eigenvalue_of_mem_spectral_tail_span S hS hn i x hx
      (by simpa [KS, Finset.coe_image, Finset.coe_Ici, Set.Ici] using hxKS)
  have hperturbX := abs_rayleighQuotient_sub_le_operatorNorm T S x
  have hUpper : hT.eigenvalues hn i ≤ hS.eigenvalues hn i + ‖T - S‖ := by
    have hdiff := (abs_le.mp hperturbX).2
    linarith
  have hsumST : finrank ℝ E < finrank ℝ HS + finrank ℝ KT := by
    rw [hdimHS, hdimKT, hn]
    omega
  obtain ⟨y, hy, hyHS, hyKT⟩ :=
    exists_ne_zero_mem_inf_of_finrank_add_gt HS KT hsumST
  have hprefixS : hS.eigenvalues hn i ≤ S.rayleighQuotient y :=
    eigenvalue_le_rayleighQuotient_of_mem_spectral_head_span S hS hn i y hy
      (by simpa [HS, Finset.coe_image, Finset.coe_Iic, Set.Iic] using hyHS)
  have htailT : T.rayleighQuotient y ≤ hT.eigenvalues hn i :=
    rayleighQuotient_le_eigenvalue_of_mem_spectral_tail_span T hT hn i y hy
      (by simpa [KT, Finset.coe_image, Finset.coe_Ici, Set.Ici] using hyKT)
  have hperturbY := abs_rayleighQuotient_sub_le_operatorNorm T S y
  have hLower : hS.eigenvalues hn i ≤ hT.eigenvalues hn i + ‖T - S‖ := by
    have hdiff := (abs_le.mp hperturbY).1
    linarith
  have hUpperDiff : hT.eigenvalues hn i - hS.eigenvalues hn i ≤ ‖T - S‖ := by
    linarith
  have hLowerDiff : -(‖T - S‖) ≤ hT.eigenvalues hn i - hS.eigenvalues hn i := by
    linarith
  exact abs_le.mpr ⟨hLowerDiff, hUpperDiff⟩

end JinWishart
