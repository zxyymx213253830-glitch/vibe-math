import JinWishartFormalization.HermitianSpectralLogDet

/-! Ordered spectral second moment equals the real trace of the square.
Codex deterministic algebra; no positivity, rank or probability assumption. -/
open Matrix
namespace JinWishart
noncomputable section

theorem hermitian_trace_square_eq_orderedEigenvalues {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    (A^2).trace.re = ∑ i, (hA.eigenvalues₀ i)^2 := by
  classical
  let U := hA.eigenvectorUnitary
  let D : Matrix (Fin n) (Fin n) ℂ := diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  have he : A^2 = Unitary.conjStarAlgAut ℂ _ U (D^2) := by
    rw [map_pow,← hA.spectral_theorem]
  rw [he,Unitary.conjStarAlgAut_apply,trace_mul_cycle,Unitary.coe_star_mul_self,one_mul]
  dsimp only [D]
  rw [Matrix.diagonal_pow,Matrix.trace_diagonal]
  simp only [Pi.pow_apply,Function.comp_apply,Complex.re_sum]
  change (∑ i, RCLike.re ((hA.eigenvalues i : ℂ)^2)) = _
  have hreal (t : ℝ) : RCLike.re ((t : ℂ)^2) = t^2 := by
    change ((t : ℂ)^2).re = t^2
    norm_cast
  simp_rw [hreal]
  simpa only [Matrix.IsHermitian.eigenvalues] using
    Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))).symm
      (fun i => (hA.eigenvalues₀ i)^2)

end
end JinWishart
#print axioms JinWishart.hermitian_trace_square_eq_orderedEigenvalues
