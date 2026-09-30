import JinWishartFormalization.SpectralRayleighCoordinates

/-!
# Lower Rayleigh bound on a spectral prefix

This is the complementary local estimate to the tail-support bound in
`SpectralRayleighCoordinates`. It uses only the actual orthonormal eigenbasis
provided by Mathlib for finite-dimensional symmetric operators.
-/

namespace JinWishart

/-- A vector supported in the first `i+1` ordered spectral coordinates has
Rayleigh quotient at least the `i`th eigenvalue. -/
theorem eigenvalue_le_rayleighQuotient_of_spectral_prefix_support
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ}
    (T : E →L[ℝ] E) (hT : (T : E →ₗ[ℝ] E).IsSymmetric)
    (hn : Module.finrank ℝ E = n) (i : Fin n) (x : E) (hx : x ≠ 0)
    (hsupport : ∀ j, i < j → (hT.eigenvectorBasis hn).repr x j = 0) :
    hT.eigenvalues hn i ≤ T.rayleighQuotient x := by
  let b := hT.eigenvectorBasis hn
  let c : Fin n → ℝ := fun j => b.repr x j
  have hcne : ∃ j, c j ≠ 0 := by
    by_contra h
    push Not at h
    have hrepr : b.repr x = 0 := by
      ext j
      simpa [c] using h j
    have hrepr' : b.repr x = b.repr 0 := by simpa using hrepr
    exact hx (b.repr.injective hrepr')
  have hnum : T.reApplyInnerSelf x =
      ∑ j, hT.eigenvalues hn j * (c j) ^ 2 := by
    have hreal : T.reApplyInnerSelf x = inner ℝ (T x) x := by
      have h := hT.coe_reApplyInnerSelf_apply x
      simpa using h
    rw [hreal]
    rw [← b.sum_inner_mul_inner (T x) x]
    apply Finset.sum_congr rfl
    intro j hj
    have hcoord : b.repr (T x) j = hT.eigenvalues hn j * b.repr x j := by
      simpa [b] using hT.eigenvectorBasis_apply_self_apply hn x j
    have hfirst : inner ℝ (T x) (b j) = b.repr (T x) j := by
      rw [real_inner_comm]
      exact (b.repr_apply_apply (T x) j).symm
    have hsecond : inner ℝ (b j) x = b.repr x j :=
      (b.repr_apply_apply x j).symm
    rw [hfirst, hsecond, hcoord]
    dsimp [c]
    ring
  have hden : ‖x‖ ^ 2 = ∑ j, (c j) ^ 2 := by
    rw [← b.sum_sq_inner_right]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← b.repr_apply_apply x j]
  rw [ContinuousLinearMap.rayleighQuotient, hnum, hden]
  exact spectral_weighted_average_ge (hT.eigenvalues hn) c i
    (hT.eigenvalues_antitone hn) (by simpa [c, b] using hsupport) hcne

end JinWishart
