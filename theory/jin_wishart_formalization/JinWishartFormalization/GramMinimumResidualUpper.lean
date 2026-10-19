import JinWishartFormalization.LeaveOneOutGramResidual

/-!
# A leave-one-out residual is at most dimension times the least Gram eigenvalue

Codex finite-dimensional spectral/projection proofs. No rank premise.
[需人工审查] Later actual Gaussian event/probability correspondence.
-/
open Matrix
open scoped ComplexOrder
namespace JinWishart
noncomputable section

def gramSmallestValue {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (hn : 0 < n) : ℝ :=
  (complexGram_posSemidef A).isHermitian.eigenvalues₀ (smallestEigenvalue₀Index hn)

theorem gram_columnMap_energy {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (u : EuclideanSpace ℂ (Fin n)) :
    ‖A.toEuclideanLin u‖^2 = (star (⇑u) ⬝ᵥ ((complexGram A) *ᵥ ⇑u)).re := by
  calc
    _ = (inner ℂ (A.toEuclideanLin u) (A.toEuclideanLin u)).re := by
      simp only [inner_self_eq_norm_sq_to_K,Complex.ofReal_pow,Complex.ofReal_re]
      norm_cast
    _ = _ := by
      congr 1
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      rw [dotProduct_comm]
      change star (A *ᵥ ⇑u) ⬝ᵥ (A *ᵥ ⇑u) = _
      rw [star_mulVec,← dotProduct_mulVec,mulVec_mulVec]
      rfl

theorem exists_gram_minimum_unit_vector {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (hn : 0 < n) :
    ∃ u : EuclideanSpace ℂ (Fin n), ‖u‖=1 ∧ ‖A.toEuclideanLin u‖^2 = gramSmallestValue A hn := by
  classical
  let hG := (complexGram_posSemidef A).isHermitian
  let e : Fin (Fintype.card (Fin n)) ≃ Fin n :=
    Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))
  let i := e (smallestEigenvalue₀Index hn)
  refine ⟨hG.eigenvectorBasis i,hG.eigenvectorBasis.orthonormal.1 i,?_⟩
  rw [gram_columnMap_energy]
  calc
    _ = hG.eigenvalues i := (hG.eigenvalues_eq i).symm
    _ = _ := by
      simp only [Matrix.IsHermitian.eigenvalues,i,e,Equiv.symm_apply_apply,gramSmallestValue,hG]

theorem exists_leaveOneOut_energy_le_dimension_mul_minimum {m n : ℕ}
    (A : Matrix (Fin m) (Fin (n+1)) ℂ) :
    ∃ j, leaveOneOutResidualEnergy A j ≤ ((n+1 : ℕ) : ℝ)*gramSmallestValue A (Nat.succ_pos n) := by
  obtain ⟨u,hu,he⟩ := exists_gram_minimum_unit_vector A (Nat.succ_pos n)
  obtain ⟨j,hj⟩ := exists_leaveOneOut_energy_le_dimension_mul A u hu
  exact ⟨j,he ▸ hj⟩

end
end JinWishart
#print axioms JinWishart.gram_columnMap_energy
#print axioms JinWishart.exists_gram_minimum_unit_vector
#print axioms JinWishart.exists_leaveOneOut_energy_le_dimension_mul_minimum
