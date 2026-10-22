import JinWishartFormalization.CanonicalFinGramTransport
import JinWishartFormalization.CanonicalShearNorm
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! Fin representations of the explicit canonical shear. Empty dimensions allowed.
The control is a squared Euclidean operator norm, not a default matrix norm.
[需人工审查] Subsequent random-factor integration and inverse-moment transport. -/
open Matrix
namespace JinWishart
noncomputable section

def canonicalFinShear {b c n : ℕ} (e : (Fin b ⊕ Fin c) ≃ Fin n)
    (K : Matrix (Fin c) (Fin b) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.reindexLinearEquiv ℂ ℂ e e (fromBlocks 1 0 K 1)

private theorem reindex_action {b c n : ℕ} (e : (Fin b ⊕ Fin c) ≃ Fin n)
    (S : Matrix (Fin b ⊕ Fin c) (Fin b ⊕ Fin c) ℂ)
    (v : EuclideanSpace ℂ (Fin n)) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (Matrix.reindexLinearEquiv ℂ ℂ e e S) v =
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e)
        (Matrix.toEuclideanCLM (𝕜 := ℂ) S
          ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).symm v)) := by
  ext i
  change (∑ j : Fin n, S (e.symm i) (e.symm j)*v j)=
    ∑ k : Fin b ⊕ Fin c, S (e.symm i) k*v (e k)
  exact Fintype.sum_equiv e.symm _ _ (by intro j; simp)

private theorem reindex_opNorm_le {b c n : ℕ} (e : (Fin b ⊕ Fin c) ≃ Fin n)
    (S : Matrix (Fin b ⊕ Fin c) (Fin b ⊕ Fin c) ℂ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (Matrix.reindexLinearEquiv ℂ ℂ e e S)‖ ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) S‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  rw [reindex_action, LinearIsometryEquiv.norm_map]
  have h := (Matrix.toEuclideanCLM (𝕜 := ℂ) S).le_opNorm
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).symm v)
  simpa only [LinearIsometryEquiv.norm_map] using h

theorem canonical_fin_shear_inverse {b c n : ℕ} (e : (Fin b ⊕ Fin c) ≃ Fin n)
    (K : Matrix (Fin c) (Fin b) ℂ) :
    canonicalFinShear e (-K)*canonicalFinShear e K=1 ∧
    canonicalFinShear e K*canonicalFinShear e (-K)=1 ∧
    (canonicalFinShear e (-K))⁻¹=canonicalFinShear e K := by
  obtain ⟨hm,hp⟩ := canonical_block_shear_two_sided_inverse K
  have hm' : canonicalFinShear e (-K)*canonicalFinShear e K=1 := by
    unfold canonicalFinShear
    rw [Matrix.reindexLinearEquiv_mul, hm, Matrix.reindexLinearEquiv_one]
  have hp' : canonicalFinShear e K*canonicalFinShear e (-K)=1 := by
    unfold canonicalFinShear
    rw [Matrix.reindexLinearEquiv_mul, hp, Matrix.reindexLinearEquiv_one]
  exact ⟨hm',hp',Matrix.inv_eq_left_inv hp'⟩

theorem canonical_fin_shear_opNorm_le {b c n : ℕ} (e : (Fin b ⊕ Fin c) ≃ Fin n)
    (K : Matrix (Fin c) (Fin b) ℂ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (canonicalFinShear e K)‖ ≤
      1+‖(Matrix.toEuclideanLin K).toContinuousLinearMap‖ ∧
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (canonicalFinShear e (-K))‖ ≤
      1+‖(Matrix.toEuclideanLin K).toContinuousLinearMap‖ := by
  constructor
  · exact (reindex_opNorm_le e _).trans (canonical_shear_opNorm_le K)
  · exact (reindex_opNorm_le e _).trans (canonical_inverse_shear_opNorm_le K)

theorem canonical_fin_shear_control_le {b c n : ℕ} (e : (Fin b ⊕ Fin c) ≃ Fin n)
    (K : Matrix (Fin c) (Fin b) ℂ) :
    matrixColumnControl (canonicalFinShear e (-K)) ≤
      (1+‖(Matrix.toEuclideanLin K).toContinuousLinearMap‖)^2 ∧
    matrixColumnControl ((canonicalFinShear e (-K))⁻¹) ≤
      (1+‖(Matrix.toEuclideanLin K).toContinuousLinearMap‖)^2 := by
  obtain ⟨hp,hm⟩ := canonical_fin_shear_opNorm_le e K
  have h1 : (1 : ℝ) ≤ (1+‖(Matrix.toEuclideanLin K).toContinuousLinearMap‖)^2 := by
    nlinarith [norm_nonneg (Matrix.toEuclideanLin K).toContinuousLinearMap]
  rw [(canonical_fin_shear_inverse e K).2.2]
  constructor
  · exact max_le h1 (pow_le_pow_left₀ (norm_nonneg _) hm 2)
  · exact max_le h1 (pow_le_pow_left₀ (norm_nonneg _) hp 2)

end
end JinWishart
#print axioms JinWishart.canonical_fin_shear_inverse
#print axioms JinWishart.canonical_fin_shear_opNorm_le
#print axioms JinWishart.canonical_fin_shear_control_le
