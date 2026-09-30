import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Rayleigh bounds in ordered spectral coordinates

This file isolates the finite weighted-average step used by the Rayleigh quotient
argument.  A remaining bridge is to identify the quotient of an arbitrary vector
in an eigenvector subspace with this weighted average.
-/

namespace JinWishart

/-- Weighted-average form of the lower Rayleigh estimate on the first `i+1`
ordered spectral coordinates. -/
theorem spectral_weighted_average_ge
    {n : ℕ} (eig c : Fin n → ℝ) (i : Fin n)
    (heig : Antitone eig)
    (hc : ∀ j, i < j → c j = 0)
    (hcne : ∃ j, c j ≠ 0) :
    eig i ≤ (∑ j, eig j * (c j) ^ 2) / (∑ j, (c j) ^ 2) := by
  have hden : 0 < ∑ j, (c j) ^ 2 := by
    apply Finset.sum_pos'
    · intro j hj
      positivity
    · obtain ⟨j, hj⟩ := hcne
      refine ⟨j, Finset.mem_univ j, ?_⟩
      have : 0 < (c j) ^ 2 := sq_pos_of_ne_zero hj
      simpa using this
  have hsum : (∑ j, eig i * (c j) ^ 2) ≤ ∑ j, eig j * (c j) ^ 2 := by
    apply Finset.sum_le_sum
    intro j hj
    by_cases hij : i < j
    · simp [hc j hij]
    · have hji : j ≤ i := le_of_not_gt hij
      have horder : eig i ≤ eig j := heig hji
      exact mul_le_mul_of_nonneg_right horder (sq_nonneg (c j))
  have hmul : eig i * ∑ j, (c j) ^ 2 ≤ ∑ j, eig j * (c j) ^ 2 := by
    calc
      eig i * ∑ j, (c j) ^ 2 = ∑ j, eig i * (c j) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ ∑ j, eig j * (c j) ^ 2 := hsum
  exact (le_div_iff₀ hden).2 (by simpa using hmul)

/-- Weighted-average form of the upper Rayleigh estimate on the coordinates
`i, …, n-1`. -/
theorem spectral_weighted_average_le
    {n : ℕ} (eig c : Fin n → ℝ) (i : Fin n)
    (heig : Antitone eig)
    (hc : ∀ j, j < i → c j = 0)
    (hcne : ∃ j, c j ≠ 0) :
    (∑ j, eig j * (c j) ^ 2) / (∑ j, (c j) ^ 2) ≤ eig i := by
  have hden : 0 < ∑ j, (c j) ^ 2 := by
    apply Finset.sum_pos'
    · intro j hj
      positivity
    · obtain ⟨j, hj⟩ := hcne
      refine ⟨j, Finset.mem_univ j, ?_⟩
      have : 0 < (c j) ^ 2 := sq_pos_of_ne_zero hj
      simpa using this
  have hsum : (∑ j, eig j * (c j) ^ 2) ≤ ∑ j, eig i * (c j) ^ 2 := by
    apply Finset.sum_le_sum
    intro j hj
    by_cases hji : j < i
    · simp [hc j hji]
    · have hij : i ≤ j := le_of_not_gt hji
      have horder : eig j ≤ eig i := heig hij
      exact mul_le_mul_of_nonneg_right horder (sq_nonneg (c j))
  have hmul : (∑ j, eig j * (c j) ^ 2) ≤ eig i * ∑ j, (c j) ^ 2 := by
    calc
      (∑ j, eig j * (c j) ^ 2) ≤ ∑ j, eig i * (c j) ^ 2 := hsum
      _ = eig i * ∑ j, (c j) ^ 2 := by rw [Finset.mul_sum]
  exact (div_le_iff₀ hden).2 (by simpa using hmul)

/-- The upper Rayleigh estimate for a vector whose ordered spectral coordinates
below index `i` vanish.  This real-inner-product version is the direct bridge
from the orthonormal eigenbasis to the weighted-average estimate above. -/
theorem rayleighQuotient_le_eigenvalue_of_spectral_support
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ}
    (T : E →L[ℝ] E) (hT : (T : E →ₗ[ℝ] E).IsSymmetric)
    (hn : Module.finrank ℝ E = n) (i : Fin n) (x : E) (hx : x ≠ 0)
    (hsupport : ∀ j, j < i → (hT.eigenvectorBasis hn).repr x j = 0) :
    T.rayleighQuotient x ≤ hT.eigenvalues hn i := by
  let b := hT.eigenvectorBasis hn
  let c : Fin n → ℝ := fun j => b.repr x j
  have hcne : ∃ j, c j ≠ 0 := by
    by_contra h
    push_neg at h
    have hrepr : b.repr x = 0 := by
      ext j
      simpa [c] using h j
    have hx0 : x = 0 := by
      have hrepr' : b.repr x = b.repr 0 := by simpa using hrepr
      exact b.repr.injective hrepr'
    exact hx hx0
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
  exact spectral_weighted_average_le (hT.eigenvalues hn) c i
    (hT.eigenvalues_antitone hn) (by simpa [c, b] using hsupport) hcne

end JinWishart
