import JinWishartFormalization.ActualNoncentralMeanGramLaw

/-! Codex. Seed2026102511 controls precede source. All coordinates are retained,
including repeated eigenvalues and zero-dimensional spaces.
[需人工审查] Ordered noncentrality convention and subsequent model mapping. -/
open Matrix
namespace JinWishart
noncomputable section

theorem hermitian_eigenvalues₀_eq_of_charpoly_eq {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : A.charpoly = B.charpoly) : hA.eigenvalues₀ = hB.eigenvalues₀ := by
  apply List.ofFn_inj.mp
  rw [← hA.sort_roots_charpoly_eq_eigenvalues₀,
    ← hB.sort_roots_charpoly_eq_eigenvalues₀, h]

theorem hermitian_eigenvalues₀_unitary_conjugation {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian)
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    (Matrix.isHermitian_conjTranspose_mul_mul (U : Matrix (Fin n) (Fin n) ℂ) hA).eigenvalues₀ =
      hA.eigenvalues₀ := by
  apply hermitian_eigenvalues₀_eq_of_charpoly_eq
  rw [Matrix.charpoly_mul_comm, Matrix.mul_assoc]
  simp only [← Matrix.mul_assoc, ← Unitary.coe_star, Unitary.coe_self_mul_star,
    Matrix.one_mul]

theorem exists_unitary_conjugation_of_eigenvalues₀_eq {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : hA.eigenvalues₀ = hB.eigenvalues₀) :
    ∃ U : Matrix.unitaryGroup (Fin n) ℂ,
      B = (U : Matrix (Fin n) (Fin n) ℂ)ᴴ * A * U := by
  have he : hA.eigenvalues = hB.eigenvalues := by
    unfold Matrix.IsHermitian.eigenvalues
    rw [h]
  refine ⟨hA.eigenvectorUnitary * star hB.eigenvectorUnitary, ?_⟩
  change B = Unitary.conjStarAlgAut ℂ _
    (star (hA.eigenvectorUnitary * star hB.eigenvectorUnitary)) A
  rw [hA.spectral_theorem, ← Unitary.conjStarAlgAut_mul_apply]
  simp only [star_mul, star_star, mul_assoc, star_mul_self, mul_one]
  rw [he]
  exact hB.spectral_theorem

end
end JinWishart
#print axioms JinWishart.hermitian_eigenvalues₀_eq_of_charpoly_eq
#print axioms JinWishart.hermitian_eigenvalues₀_unitary_conjugation
#print axioms JinWishart.exists_unitary_conjugation_of_eigenvalues₀_eq
