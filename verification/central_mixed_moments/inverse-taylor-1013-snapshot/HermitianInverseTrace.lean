import JinWishartFormalization.HermitianSquaredTrace

/-! Trace of ordinary matrix inverse powers from a nonzero Hermitian spectrum.
Codex deterministic algebra, not a pseudoinverse or an expectation assertion.
-/
open Matrix
namespace JinWishart
noncomputable section

theorem hermitian_trace_inverse_pow_eq_orderedEigenvalues {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (hnz : ∀ i, hA.eigenvalues₀ i ≠ 0) (k : ℕ) :
    ((A⁻¹)^k).trace.re = ∑ i, ((hA.eigenvalues₀ i)⁻¹)^k := by
  classical
  let U := hA.eigenvectorUnitary
  let D : Matrix (Fin n) (Fin n) ℂ := diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  let E : Matrix (Fin n) (Fin n) ℂ := diagonal (fun i => ((hA.eigenvalues i)⁻¹ : ℝ))
  have hn (i : Fin n) : hA.eigenvalues i ≠ 0 := hnz _
  have hDE : D*E=1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i=j
    · subst j
      simp [hn i]
    · simp [hij]
  have hAE : A * Unitary.conjStarAlgAut ℂ _ U E=1 := by
    calc
      _ = Unitary.conjStarAlgAut ℂ _ U D * Unitary.conjStarAlgAut ℂ _ U E := by
        rw [hA.spectral_theorem]
      _ = Unitary.conjStarAlgAut ℂ _ U (D*E) := (map_mul _ _ _).symm
      _ = 1 := by rw [hDE,map_one]
  have hi : A⁻¹=Unitary.conjStarAlgAut ℂ _ U E := Matrix.inv_eq_right_inv hAE
  rw [hi,← map_pow,Unitary.conjStarAlgAut_apply,trace_mul_cycle,
    Unitary.coe_star_mul_self,one_mul]
  dsimp only [E]
  rw [Matrix.diagonal_pow,Matrix.trace_diagonal]
  simp only [Pi.pow_apply,Complex.re_sum]
  change (∑ i : Fin n, ((((hA.eigenvalues i)⁻¹:ℝ):ℂ)^k).re)=_
  simp only [← Complex.ofReal_pow,Complex.ofReal_re]
  simpa only [Matrix.IsHermitian.eigenvalues] using
    Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))).symm
      (fun i => ((hA.eigenvalues₀ i)⁻¹)^k)

end
end JinWishart
#print axioms JinWishart.hermitian_trace_inverse_pow_eq_orderedEigenvalues
