import JinWishartFormalization.CanonicalBlockShear
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! Euclidean operator norm control for a block shear. Empty dimensions allowed.
Pure deterministic bound; no Gaussian moment or inverse-moment transport. -/
open Matrix
namespace JinWishart
noncomputable section
variable {b c : ℕ}

private abbrev rectCLM (K : Matrix (Fin c) (Fin b) ℂ) :=
  (Matrix.toEuclideanLin K).toContinuousLinearMap

private theorem left_norm_le (u : EuclideanSpace ℂ (Fin b ⊕ Fin c)) :
    ‖(WithLp.toLp 2 (fun i : Fin b => u (Sum.inl i)) : EuclideanSpace ℂ (Fin b))‖ ≤ ‖u‖ := by
  let ul : EuclideanSpace ℂ (Fin b) := WithLp.toLp 2 (fun i => u (Sum.inl i))
  let ur : EuclideanSpace ℂ (Fin c) := WithLp.toLp 2 (fun i => u (Sum.inr i))
  have hs : ‖u‖^2 = ‖ul‖^2 + ‖ur‖^2 := by
    simp [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type, ul, ur]
  have hp := sq_nonneg ‖ur‖
  change ‖ul‖ ≤ ‖u‖
  nlinarith [norm_nonneg ul, norm_nonneg u]

private theorem nilpotent_norm_le (K : Matrix (Fin c) (Fin b) ℂ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (fromBlocks (0 : Matrix (Fin b) (Fin b) ℂ) 0 K 0)‖ ≤
      ‖rectCLM K‖ := by
  let J : Matrix (Fin b ⊕ Fin c) (Fin b ⊕ Fin c) ℂ := fromBlocks 0 0 K 0
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro u
  let ul : EuclideanSpace ℂ (Fin b) := WithLp.toLp 2 (fun i => u (Sum.inl i))
  have hs : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) J u‖^2 = ‖rectCLM K ul‖^2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    change (∑ i : Fin b ⊕ Fin c, ‖(J *ᵥ (⇑u)) i‖^2) =
      ∑ i : Fin c, ‖(K *ᵥ (fun j => u (Sum.inl j))) i‖^2
    simp [J, fromBlocks_mulVec, Fintype.sum_sum_type, Function.comp_def]
  have he : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) J u‖ = ‖rectCLM K ul‖ :=
    (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs
  change ‖Matrix.toEuclideanCLM (𝕜 := ℂ) J u‖ ≤ _
  rw [he]
  exact ((rectCLM K).le_opNorm ul).trans
    (mul_le_mul_of_nonneg_left (left_norm_le u) (norm_nonneg _))

theorem canonical_shear_opNorm_le (K : Matrix (Fin c) (Fin b) ℂ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (fromBlocks 1 0 K 1)‖ ≤
      1 + ‖(Matrix.toEuclideanLin K).toContinuousLinearMap‖ := by
  let J : Matrix (Fin b ⊕ Fin c) (Fin b ⊕ Fin c) ℂ := fromBlocks 0 0 K 0
  have hS : fromBlocks (1 : Matrix (Fin b) (Fin b) ℂ) 0 K 1 = 1 + J := by
    ext i j
    cases i <;> cases j <;> simp [J, fromBlocks, Matrix.one_apply]
  rw [hS, map_add, map_one]
  exact (norm_add_le _ _).trans (add_le_add ContinuousLinearMap.norm_id_le (nilpotent_norm_le K))

theorem canonical_inverse_shear_opNorm_le (K : Matrix (Fin c) (Fin b) ℂ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (fromBlocks 1 0 (-K) 1)‖ ≤
      1 + ‖(Matrix.toEuclideanLin K).toContinuousLinearMap‖ := by
  have h := canonical_shear_opNorm_le (-K)
  simpa only [map_neg, norm_neg] using h

end
end JinWishart
#print axioms JinWishart.canonical_shear_opNorm_le
#print axioms JinWishart.canonical_inverse_shear_opNorm_le
