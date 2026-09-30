import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Module.FiniteDimension
import JinWishartFormalization.OrderedEigenvalueFullMeasurable
import JinWishartFormalization.SubspaceIntersectionFinrank
import JinWishartFormalization.SpectralCoordinateSpanSupport
import JinWishartFormalization.OrderedEigenvalueWeyl

/-!
# Complex Hermitian Weyl perturbation theorem

This module develops the RCLike coordinate-weight version of the finite-dimensional real
Courant--Fischer argument, with the goal of applying it to complex Hermitian matrices.
-/

namespace JinWishart

open Module Submodule
open scoped Matrix.Norms.L2Operator

private theorem weightedAverageGe {n : ℕ} (eig w : Fin n → ℝ) (i : Fin n)
    (heig : Antitone eig) (hw : ∀ j, 0 ≤ w j)
    (hsupport : ∀ j, i < j → w j = 0) (hne : ∃ j, w j ≠ 0) :
    eig i ≤ (∑ j, eig j * w j) / (∑ j, w j) := by
  have hden : 0 < ∑ j, w j := by
    apply Finset.sum_pos'
    · intro j hj
      exact hw j
    · obtain ⟨j, hj⟩ := hne
      exact ⟨j, Finset.mem_univ j, lt_of_le_of_ne (hw j) (Ne.symm hj)⟩
  have hsum : (∑ j, eig i * w j) ≤ ∑ j, eig j * w j := by
    apply Finset.sum_le_sum
    intro j hj
    by_cases hij : i < j
    · simp [hsupport j hij]
    · exact mul_le_mul_of_nonneg_right (heig (le_of_not_gt hij)) (hw j)
  have hmul : eig i * ∑ j, w j ≤ ∑ j, eig j * w j := by
    calc
      eig i * ∑ j, w j = ∑ j, eig i * w j := by rw [Finset.mul_sum]
      _ ≤ ∑ j, eig j * w j := hsum
  exact (le_div_iff₀ hden).2 (by simpa using hmul)

private theorem weightedAverageLe {n : ℕ} (eig w : Fin n → ℝ) (i : Fin n)
    (heig : Antitone eig) (hw : ∀ j, 0 ≤ w j)
    (hsupport : ∀ j, j < i → w j = 0) (hne : ∃ j, w j ≠ 0) :
    (∑ j, eig j * w j) / (∑ j, w j) ≤ eig i := by
  have hden : 0 < ∑ j, w j := by
    apply Finset.sum_pos'
    · intro j hj
      exact hw j
    · obtain ⟨j, hj⟩ := hne
      exact ⟨j, Finset.mem_univ j, lt_of_le_of_ne (hw j) (Ne.symm hj)⟩
  have hsum : (∑ j, eig j * w j) ≤ ∑ j, eig i * w j := by
    apply Finset.sum_le_sum
    intro j hj
    by_cases hji : j < i
    · simp [hsupport j hji]
    · exact mul_le_mul_of_nonneg_right (heig (le_of_not_gt hji)) (hw j)
  have hmul : (∑ j, eig j * w j) ≤ eig i * ∑ j, w j := by
    calc
      (∑ j, eig j * w j) ≤ ∑ j, eig i * w j := hsum
      _ = eig i * ∑ j, w j := by rw [Finset.mul_sum]
  exact (div_le_iff₀ hden).2 (by simpa using hmul)

private theorem rayleighUpperOfCoordinateSupport
    {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {n : ℕ}
    (T : E →L[𝕜] E) (hT : (T : E →ₗ[𝕜] E).IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) (i : Fin n) (x : E) (hx : x ≠ 0)
    (hsupport : ∀ j, j < i → (hT.eigenvectorBasis hn).repr x j = 0) :
    T.rayleighQuotient x ≤ hT.eigenvalues hn i := by
  let b := hT.eigenvectorBasis hn
  let c : Fin n → 𝕜 := fun j => b.repr x j
  let w : Fin n → ℝ := fun j => ‖c j‖ ^ 2
  have hw : ∀ j, 0 ≤ w j := fun j => sq_nonneg _
  have hne : ∃ j, w j ≠ 0 := by
    by_contra h
    push_neg at h
    have hrepr : b.repr x = 0 := by
      ext j
      have hc : c j = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp (h j))
      simpa [c] using hc
    exact hx (b.repr.injective (by simpa using hrepr))
  have hnum : T.reApplyInnerSelf x = ∑ j, hT.eigenvalues hn j * w j := by
    rw [T.reApplyInnerSelf_apply]
    rw [← b.sum_inner_mul_inner (T x) x]
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hcoord : b.repr (T x) j = (hT.eigenvalues hn j : 𝕜) * b.repr x j := by
      simpa [b] using hT.eigenvectorBasis_apply_self_apply hn x j
    have hfirst : inner 𝕜 (T x) (b j) = star (b.repr (T x) j) := by
      rw [← inner_conj_symm, ← b.repr_apply_apply (T x) j]
      rfl
    have hsecond : inner 𝕜 (b j) x = b.repr x j :=
      (b.repr_apply_apply x j).symm
    rw [hfirst, hsecond, hcoord]
    have hnorm : ‖c j‖ ^ 2 = RCLike.re (star (c j) * c j) := by
      simpa [inner, mul_comm] using
        (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := 𝕜) (x := c j))
    simp [w, c, hnorm, star_mul, mul_comm, mul_left_comm, mul_assoc]
    ring
  have hden : ‖x‖ ^ 2 = ∑ j, w j := by
    rw [← b.sum_sq_norm_inner_right x]
    apply Finset.sum_congr rfl
    intro j hj
    simp [w, c, b.repr_apply_apply]
  rw [ContinuousLinearMap.rayleighQuotient, hnum, hden]
  apply weightedAverageLe (hT.eigenvalues hn) w i (hT.eigenvalues_antitone hn) hw
  · intro j hji
    simpa [w, c, b, hsupport j hji]
  · exact hne

private theorem rayleighLowerOfCoordinateSupport
    {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {n : ℕ}
    (T : E →L[𝕜] E) (hT : (T : E →ₗ[𝕜] E).IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) (i : Fin n) (x : E) (hx : x ≠ 0)
    (hsupport : ∀ j, i < j → (hT.eigenvectorBasis hn).repr x j = 0) :
    hT.eigenvalues hn i ≤ T.rayleighQuotient x := by
  let b := hT.eigenvectorBasis hn
  let c : Fin n → 𝕜 := fun j => b.repr x j
  let w : Fin n → ℝ := fun j => ‖c j‖ ^ 2
  have hw : ∀ j, 0 ≤ w j := fun j => sq_nonneg _
  have hne : ∃ j, w j ≠ 0 := by
    by_contra h
    push_neg at h
    have hrepr : b.repr x = 0 := by
      ext j
      have hc : c j = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp (h j))
      simpa [c] using hc
    exact hx (b.repr.injective (by simpa using hrepr))
  have hnum : T.reApplyInnerSelf x = ∑ j, hT.eigenvalues hn j * w j := by
    rw [T.reApplyInnerSelf_apply]
    rw [← b.sum_inner_mul_inner (T x) x]
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hcoord : b.repr (T x) j = (hT.eigenvalues hn j : 𝕜) * b.repr x j := by
      simpa [b] using hT.eigenvectorBasis_apply_self_apply hn x j
    have hfirst : inner 𝕜 (T x) (b j) = star (b.repr (T x) j) := by
      rw [← inner_conj_symm, ← b.repr_apply_apply (T x) j]
      rfl
    have hsecond : inner 𝕜 (b j) x = b.repr x j :=
      (b.repr_apply_apply x j).symm
    rw [hfirst, hsecond, hcoord]
    have hnorm : ‖c j‖ ^ 2 = RCLike.re (star (c j) * c j) := by
      simpa [inner, mul_comm] using
        (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := 𝕜) (x := c j))
    simp [w, c, hnorm, star_mul, mul_comm, mul_left_comm]
    ring
  have hden : ‖x‖ ^ 2 = ∑ j, w j := by
    rw [← b.sum_sq_norm_inner_right x]
    apply Finset.sum_congr rfl
    intro j hj
    simp [w, c, b.repr_apply_apply]
  rw [ContinuousLinearMap.rayleighQuotient, hnum, hden]
  apply weightedAverageGe (hT.eigenvalues hn) w i (hT.eigenvalues_antitone hn) hw
  · intro j hij
    simp [w, c, b, hsupport j hij]
  · exact hne

private theorem finrank_spectralHeadSpan
    {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [DecidableEq E] {n : ℕ}
    (T : E →L[𝕜] E) (hT : (T : E →ₗ[𝕜] E).IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) (i : Fin n) :
    Module.finrank 𝕜 (span 𝕜 (((Finset.Iic i).image (hT.eigenvectorBasis hn).toBasis : Finset E) : Set E))
      = i.val + 1 := by
  classical
  let c := Finset.Iic i
  have hlin : LinearIndependent 𝕜 (fun j : c => (hT.eigenvectorBasis hn).toBasis j.1) :=
    (hT.eigenvectorBasis hn).toBasis.linearIndependent.comp
      Subtype.val Subtype.val_injective
  have hrange : Set.range (fun j : c => (hT.eigenvectorBasis hn).toBasis j.1) =
      ((c.image (hT.eigenvectorBasis hn).toBasis : Finset E) : Set E) := by
    ext x
    simp [c]
  change Module.finrank 𝕜 ↥(span 𝕜
    ((c.image (hT.eigenvectorBasis hn).toBasis : Finset E) : Set E)) = i.val + 1
  rw [← hrange]
  have hdim := finrank_span_eq_card hlin
  rw [Fintype.card_coe, Fin.card_Iic] at hdim
  exact hdim

private theorem finrank_spectralTailSpan
    {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [DecidableEq E] {n : ℕ}
    (T : E →L[𝕜] E) (hT : (T : E →ₗ[𝕜] E).IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) (i : Fin n) :
    Module.finrank 𝕜 (span 𝕜 (((Finset.Ici i).image (hT.eigenvectorBasis hn).toBasis : Finset E) : Set E))
      = n - i.val := by
  classical
  let c := Finset.Ici i
  have hlin : LinearIndependent 𝕜 (fun j : c => (hT.eigenvectorBasis hn).toBasis j.1) :=
    (hT.eigenvectorBasis hn).toBasis.linearIndependent.comp
      Subtype.val Subtype.val_injective
  have hrange : Set.range (fun j : c => (hT.eigenvectorBasis hn).toBasis j.1) =
      ((c.image (hT.eigenvectorBasis hn).toBasis : Finset E) : Set E) := by
    ext x
    simp [c]
  change Module.finrank 𝕜 ↥(span 𝕜
    ((c.image (hT.eigenvectorBasis hn).toBasis : Finset E) : Set E)) = n - i.val
  rw [← hrange]
  have hdim := finrank_span_eq_card hlin
  rw [Fintype.card_coe, Fin.card_Ici] at hdim
  exact hdim

/-- For a finite-dimensional inner-product space over either `ℝ` or `ℂ`, every ordered eigenvalue
is Lipschitz with respect to the operator norm. The proof is the indexed head/tail intersection
argument, using the eigenbasis coordinate Rayleigh bounds above. -/
theorem abs_eigenvalue_sub_le_operatorNorm_rclike
    {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    {n : ℕ} (T S : E →L[𝕜] E)
    (hT : (T : E →ₗ[𝕜] E).IsSymmetric) (hS : (S : E →ₗ[𝕜] E).IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) (i : Fin n) :
    |hT.eigenvalues hn i - hS.eigenvalues hn i| ≤ ‖T - S‖ := by
  classical
  let HT : Submodule 𝕜 E := span 𝕜 ((Finset.Iic i).image (hT.eigenvectorBasis hn).toBasis)
  let KS : Submodule 𝕜 E := span 𝕜 ((Finset.Ici i).image (hS.eigenvectorBasis hn).toBasis)
  let HS : Submodule 𝕜 E := span 𝕜 ((Finset.Iic i).image (hS.eigenvectorBasis hn).toBasis)
  let KT : Submodule 𝕜 E := span 𝕜 ((Finset.Ici i).image (hT.eigenvectorBasis hn).toBasis)
  have hdimHT : Module.finrank 𝕜 HT = i.val + 1 := by
    simpa [HT] using finrank_spectralHeadSpan T hT hn i
  have hdimKS : Module.finrank 𝕜 KS = n - i.val := by
    simpa [KS] using finrank_spectralTailSpan S hS hn i
  have hdimHS : Module.finrank 𝕜 HS = i.val + 1 := by
    simpa [HS] using finrank_spectralHeadSpan S hS hn i
  have hdimKT : Module.finrank 𝕜 KT = n - i.val := by
    simpa [KT] using finrank_spectralTailSpan T hT hn i
  have hsumTS : Module.finrank 𝕜 E < Module.finrank 𝕜 HT + Module.finrank 𝕜 KS := by
    rw [hdimHT, hdimKS, hn]
    omega
  obtain ⟨x, hx, hxHT, hxKS⟩ :=
    exists_ne_zero_mem_inf_of_finrank_add_gt HT KS hsumTS
  have hxHeadT : x ∈ span 𝕜 ((hT.eigenvectorBasis hn) '' Set.Iic i) := by
    simpa [HT, Finset.coe_image, Finset.coe_Iic, Set.Iic] using hxHT
  have hxTailS : x ∈ span 𝕜 ((hS.eigenvectorBasis hn) '' Set.Ici i) := by
    simpa [KS, Finset.coe_image, Finset.coe_Ici, Set.Ici] using hxKS
  have hprefixT : hT.eigenvalues hn i ≤ T.rayleighQuotient x :=
    rayleighLowerOfCoordinateSupport T hT hn i x hx (by
      intro j hji
      have hspan : x ∈ span 𝕜 ((hT.eigenvectorBasis hn).toBasis '' Set.Iic i) := by
        simpa only [OrthonormalBasis.coe_toBasis] using hxHeadT
      exact basis_repr_eq_zero_of_mem_span_not_mem (hT.eigenvectorBasis hn).toBasis
        (Set.Iic i) hspan (by simp [Set.mem_Iic, not_le.mpr hji]))
  have htailS : S.rayleighQuotient x ≤ hS.eigenvalues hn i :=
    rayleighUpperOfCoordinateSupport S hS hn i x hx (by
      intro j hji
      have hspan : x ∈ span 𝕜 ((hS.eigenvectorBasis hn).toBasis '' Set.Ici i) := by
        simpa only [OrthonormalBasis.coe_toBasis] using hxTailS
      exact basis_repr_eq_zero_of_mem_span_not_mem (hS.eigenvectorBasis hn).toBasis
        (Set.Ici i) hspan (by simp [Set.mem_Ici, not_le.mpr hji]))
  have hperturbX := abs_rayleighQuotient_sub_le_operatorNorm T S x
  have hUpper : hT.eigenvalues hn i ≤ hS.eigenvalues hn i + ‖T - S‖ := by
    have hdiff := (abs_le.mp hperturbX).2
    linarith
  have hsumST : Module.finrank 𝕜 E < Module.finrank 𝕜 HS + Module.finrank 𝕜 KT := by
    rw [hdimHS, hdimKT, hn]
    omega
  obtain ⟨y, hy, hyHS, hyKT⟩ :=
    exists_ne_zero_mem_inf_of_finrank_add_gt HS KT hsumST
  have hyHeadS : y ∈ span 𝕜 ((hS.eigenvectorBasis hn) '' Set.Iic i) := by
    simpa [HS, Finset.coe_image, Finset.coe_Iic, Set.Iic] using hyHS
  have hyTailT : y ∈ span 𝕜 ((hT.eigenvectorBasis hn) '' Set.Ici i) := by
    simpa [KT, Finset.coe_image, Finset.coe_Ici, Set.Ici] using hyKT
  have hprefixS : hS.eigenvalues hn i ≤ S.rayleighQuotient y :=
    rayleighLowerOfCoordinateSupport S hS hn i y hy (by
      intro j hji
      have hspan : y ∈ span 𝕜 ((hS.eigenvectorBasis hn).toBasis '' Set.Iic i) := by
        simpa only [OrthonormalBasis.coe_toBasis] using hyHeadS
      exact basis_repr_eq_zero_of_mem_span_not_mem (hS.eigenvectorBasis hn).toBasis
        (Set.Iic i) hspan (by simp [Set.mem_Iic, not_le.mpr hji]))
  have htailT : T.rayleighQuotient y ≤ hT.eigenvalues hn i :=
    rayleighUpperOfCoordinateSupport T hT hn i y hy (by
      intro j hji
      have hspan : y ∈ span 𝕜 ((hT.eigenvectorBasis hn).toBasis '' Set.Ici i) := by
        simpa only [OrthonormalBasis.coe_toBasis] using hyTailT
      exact basis_repr_eq_zero_of_mem_span_not_mem (hT.eigenvectorBasis hn).toBasis
        (Set.Ici i) hspan (by simp [Set.mem_Ici, not_le.mpr hji]))
  have hperturbY := abs_rayleighQuotient_sub_le_operatorNorm T S y
  have hLower : hS.eigenvalues hn i ≤ hT.eigenvalues hn i + ‖T - S‖ := by
    have hdiff := (abs_le.mp hperturbY).1
    linarith
  have hUpperDiff : hT.eigenvalues hn i - hS.eigenvalues hn i ≤ ‖T - S‖ := by
    linarith
  have hLowerDiff : -(‖T - S‖) ≤ hT.eigenvalues hn i - hS.eigenvalues hn i := by
    linarith
  exact abs_le.mpr ⟨hLowerDiff, hUpperDiff⟩

abbrev SymmetricCLM (n : ℕ) :=
  {T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) //
    (T : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)).IsSymmetric}

private theorem eigenvalue_coord_lipschitz (n : ℕ) (i : Fin (Fintype.card (Fin n))) :
    LipschitzWith 1 (fun T : SymmetricCLM n => T.2.eigenvalues finrank_euclideanSpace i) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro T S
  have h := abs_eigenvalue_sub_le_operatorNorm_rclike T.1 S.1 T.2 S.2
    (by simp) i
  simpa [dist_eq_norm, Subtype.dist_eq] using h

private noncomputable def hermitianToSymmetricCLM (n : ℕ) :
    HermitianMatrix n → SymmetricCLM n := fun A =>
  ⟨Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A.1, by
    change (Matrix.toEuclideanLin A.1).IsSymmetric
    exact (Matrix.isSymmetric_toEuclideanLin_iff).mpr A.2⟩

private theorem continuous_hermitianToSymmetricCLM (n : ℕ) :
    Continuous (hermitianToSymmetricCLM n) := by
  have hLipschitz : LipschitzWith 1
      (fun A : Matrix (Fin n) (Fin n) ℂ =>
        Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A) := by
    apply LipschitzWith.of_dist_le_mul
    intro A B
    rw [dist_eq_norm, dist_eq_norm]
    have hsub : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A -
        Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) B =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (A - B) := by
      simp
    rw [hsub]
    rw [Matrix.l2_opNorm_toEuclideanCLM]
    norm_num
  have hmap : Continuous (fun A : HermitianMatrix n =>
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A.1) :=
    hLipschitz.continuous.comp continuous_subtype_val
  exact hmap.subtype_mk (fun A => (Matrix.isSymmetric_toEuclideanLin_iff).mpr A.2)

/-- The ordered eigenvalue coordinates are Lipschitz-continuous on the
finite-dimensional complex Hermitian matrix space, by the RCLike Weyl bound. -/
theorem orderedHermitianEigenvalueCoordinatesContinuous (n : ℕ) :
    OrderedHermitianEigenvalueCoordinatesContinuous n := by
  intro i
  have hcont : Continuous (fun A : HermitianMatrix n =>
      (hermitianToSymmetricCLM n A).2.eigenvalues finrank_euclideanSpace i) :=
    (eigenvalue_coord_lipschitz n i).continuous.comp
      (continuous_hermitianToSymmetricCLM n)
  convert hcont using 1
  funext A
  simp [hermitianToSymmetricCLM, hermitianEigenvalueVector,
    Matrix.IsHermitian.eigenvalues₀, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]

end JinWishart
