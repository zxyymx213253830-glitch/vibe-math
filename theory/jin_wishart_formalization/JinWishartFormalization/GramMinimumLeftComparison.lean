import JinWishartFormalization.GramMinimumColumnComparison

/-! Least COLUMN Gram eigenvalue under an invertible LEFT transformation.
No rank assumption on A. This does not identify a smallest positive eigenvalue
when structural zero modes exist. Codex. [需人工审查] Later model transport. -/
open Matrix
namespace JinWishart
noncomputable section

theorem matrixLeft_composition {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (T : Matrix (Fin m) (Fin m) ℂ) (u : EuclideanSpace ℂ (Fin n)) :
    (T*A).toEuclideanLin u =
      Matrix.toEuclideanCLM (n := Fin m) (𝕜 := ℂ) T (A.toEuclideanLin u) := by
  ext i
  change ((T*A)*ᵥ (⇑u)) i = (T*ᵥ (A*ᵥ (⇑u))) i
  rw [Matrix.mulVec_mulVec]

theorem gramSmallestValue_mul_left_upper {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (T : Matrix (Fin m) (Fin m) ℂ) (hn : 0<n) :
    gramSmallestValue (T*A) hn ≤ matrixColumnControl T*gramSmallestValue A hn := by
  obtain ⟨w,hw,he⟩ := exists_gram_minimum_unit_vector A hn
  have hray := gramSmallestValue_rayleigh_lower (T*A) hn w
  rw [hw,one_pow,mul_one] at hray
  have hc := matrixColumn_energy_bound T (A.toEuclideanLin w)
  rw [← matrixLeft_composition,he] at hc
  exact hray.trans hc

theorem gramSmallestValue_mul_left_lower {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (T : Matrix (Fin m) (Fin m) ℂ) (hn : 0<n) (hT : IsUnit T.det) :
    gramSmallestValue A hn ≤ matrixColumnControl T⁻¹*gramSmallestValue (T*A) hn := by
  have h := gramSmallestValue_mul_left_upper (T*A) T⁻¹ hn
  rw [← Matrix.mul_assoc,T.nonsing_inv_mul hT,Matrix.one_mul] at h
  exact h

end
end JinWishart
#print axioms JinWishart.matrixLeft_composition
#print axioms JinWishart.gramSmallestValue_mul_left_upper
#print axioms JinWishart.gramSmallestValue_mul_left_lower
