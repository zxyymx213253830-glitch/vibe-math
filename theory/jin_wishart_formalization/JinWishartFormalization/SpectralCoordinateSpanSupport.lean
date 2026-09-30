import Mathlib.Analysis.InnerProductSpace.Spectrum
import JinWishartFormalization.SpectralRayleighCoordinates
import JinWishartFormalization.SpectralRayleighPrefix

/-!
# Coordinate support of spans of basis vectors

This is the algebraic bridge needed to turn membership in a spectral prefix or
tail span into the coordinate hypotheses used by the Rayleigh quotient bounds.
-/

namespace JinWishart

open Module Submodule

theorem basis_repr_eq_zero_of_mem_span_not_mem
    {K E ι : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]
    (b : Basis ι K E) (s : Set ι) {x : E}
    (hx : x ∈ span K (b '' s)) {j : ι} (hj : j ∉ s) : b.repr x j = 0 := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with ⟨k, hk, rfl⟩
    have hkj : k ≠ j := fun h => hj (h ▸ hk)
    simp [hkj]
  · simp
  · intro x y hx hy ihx ihy
    simp [map_add, ihx, ihy]
  · intro a x hx ih
    simp [map_smul, ih]

/-- A vector in the span of the first `i+1` ordered eigenvectors has no
coordinates after index `i`, hence its Rayleigh quotient is at least the
`i`th eigenvalue. -/
theorem eigenvalue_le_rayleighQuotient_of_mem_spectral_head_span
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ}
    (T : E →L[ℝ] E) (hT : (T : E →ₗ[ℝ] E).IsSymmetric)
    (hn : Module.finrank ℝ E = n) (i : Fin n) (x : E) (hx : x ≠ 0)
    (hspan : x ∈ Submodule.span ℝ
      ((hT.eigenvectorBasis hn) '' {j : Fin n | ¬ i < j})) :
    hT.eigenvalues hn i ≤ T.rayleighQuotient x := by
  apply eigenvalue_le_rayleighQuotient_of_spectral_prefix_support T hT hn i x hx
  have hspan' : x ∈ Submodule.span ℝ
      ((hT.eigenvectorBasis hn).toBasis '' {j : Fin n | ¬ i < j}) := by
    simpa only [OrthonormalBasis.coe_toBasis] using hspan
  intro j hij
  exact basis_repr_eq_zero_of_mem_span_not_mem (hT.eigenvectorBasis hn).toBasis
    {j : Fin n | ¬ i < j} hspan' (by simpa using hij)

/-- A vector in the span of eigenvectors indexed `i,…,n-1` has no
coordinates before index `i`, hence its Rayleigh quotient is at most the
`i`th eigenvalue. -/
theorem rayleighQuotient_le_eigenvalue_of_mem_spectral_tail_span
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ}
    (T : E →L[ℝ] E) (hT : (T : E →ₗ[ℝ] E).IsSymmetric)
    (hn : Module.finrank ℝ E = n) (i : Fin n) (x : E) (hx : x ≠ 0)
    (hspan : x ∈ Submodule.span ℝ
      ((hT.eigenvectorBasis hn) '' {j : Fin n | i ≤ j})) :
    T.rayleighQuotient x ≤ hT.eigenvalues hn i := by
  apply rayleighQuotient_le_eigenvalue_of_spectral_support T hT hn i x hx
  have hspan' : x ∈ Submodule.span ℝ
      ((hT.eigenvectorBasis hn).toBasis '' {j : Fin n | i ≤ j}) := by
    simpa only [OrthonormalBasis.coe_toBasis] using hspan
  intro j hji
  exact basis_repr_eq_zero_of_mem_span_not_mem (hT.eigenvectorBasis hn).toBasis
    {j : Fin n | i ≤ j} hspan' (by simpa using hji)

end JinWishart
