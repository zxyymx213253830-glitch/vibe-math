import JinWishartFormalization.GramMinimumResidualUpper

/-! Least Gram eigenvalue bounds every column-map energy. Codex proofs.
No rank hypothesis. [需人工审查] Later actual-law correspondence.
-/
open Matrix
open scoped ComplexOrder
namespace JinWishart
noncomputable section

theorem euclidean_star_dot_self_re {n : ℕ} (u : EuclideanSpace ℂ (Fin n)) :
    (star (⇑u) ⬝ᵥ ⇑u).re = ‖u‖^2 := by
  have h := congrArg Complex.re (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) u)
  rw [EuclideanSpace.inner_eq_star_dotProduct,dotProduct_comm] at h
  norm_cast at h

theorem gramSmallestValue_rayleigh_lower {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (hn : 0 < n)
    (u : EuclideanSpace ℂ (Fin n)) :
    gramSmallestValue A hn * ‖u‖^2 ≤ ‖A.toEuclideanLin u‖^2 := by
  have hG := (complexGram_posSemidef A).isHermitian
  have he : complexGram A ∈ smallestEigenvalueTailEvent (gramSmallestValue A hn) := by
    apply (smallestEigenvalueTailEvent_iff_smallest_eigenvalue₀_ge _ hG
      (by simpa using hn) _).mpr
    exact le_rfl
  change (complexGram A-(gramSmallestValue A hn : ℂ) • 1).PosSemidef at he
  have h := he.re_dotProduct_nonneg (⇑u)
  change 0 ≤ (star (⇑u) ⬝ᵥ
    ((complexGram A-(gramSmallestValue A hn : ℂ) • 1) *ᵥ ⇑u)).re at h
  simp only [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_sub,
    dotProduct_smul,smul_eq_mul,Complex.sub_re,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at h
  rw [← gram_columnMap_energy,euclidean_star_dot_self_re] at h
  linarith

end
end JinWishart
#print axioms JinWishart.euclidean_star_dot_self_re
#print axioms JinWishart.gramSmallestValue_rayleigh_lower
