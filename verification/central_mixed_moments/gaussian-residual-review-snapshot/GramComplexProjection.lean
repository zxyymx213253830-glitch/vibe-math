import JinWishartFormalization.GaussianGramProjector

/-!
# Complex and real column-space projections agree on the full-rank locus

Codex proofs. The Gram inverse formula is used only with its explicit
nonsingularity hypothesis. [需人工审查] Real/complex projection identification.
-/
open Matrix
namespace JinWishart
noncomputable section

theorem gramInverseProjector_eq_complex_projection {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (hA : IsUnit (Aᴴ*A).det)
    (z : EuclideanSpace ℂ (Fin m)) :
    A.toEuclideanLin.range.starProjection z = (gramInverseProjector A).toEuclideanLin z := by
  let K := A.toEuclideanLin.range
  have hm : (gramInverseProjector A).toEuclideanLin z ∈ K := by
    refine ⟨((Aᴴ*A)⁻¹).toEuclideanLin (Aᴴ.toEuclideanLin z),?_⟩
    simp only [gramInverseProjector,Matrix.toEuclideanLin,Matrix.toLpLin_mul_same,
      LinearMap.comp_apply]
  have hr : z-(gramInverseProjector A).toEuclideanLin z ∈ Kᗮ := by
    rw [LinearMap.orthogonal_range]
    change A.toEuclideanLin.adjoint (z-(gramInverseProjector A).toEuclideanLin z)=0
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,map_sub]
    apply sub_eq_zero.mpr
    have h := congrArg (fun B : Matrix (Fin n) (Fin m) ℂ => B.toEuclideanLin z)
      (gramInverseProjector_normal_equation A hA)
    simpa only [Matrix.toEuclideanLin,Matrix.toLpLin_mul_same,LinearMap.comp_apply] using h.symm
  exact K.eq_starProjection_of_mem_orthogonal hm hr

theorem gramColumnProjection_complex_eq_real {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (hA : IsUnit (Aᴴ*A).det)
    (z : EuclideanSpace ℂ (Fin m)) :
    A.toEuclideanLin.range.starProjection z =
      (A.toEuclideanLin.range.restrictScalars ℝ).starProjection z := by
  rw [gramInverseProjector_eq_complex_projection A hA,
    gramInverseProjector_eq_real_projection A hA]

theorem gramColumnResidualProjection_complex_eq_real {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (hA : IsUnit (Aᴴ*A).det)
    (z : EuclideanSpace ℂ (Fin m)) :
    A.toEuclideanLin.rangeᗮ.starProjection z =
      (A.toEuclideanLin.range.restrictScalars ℝ)ᗮ.starProjection z := by
  have hC := A.toEuclideanLin.range.starProjection_add_starProjection_orthogonal z
  have hR := (A.toEuclideanLin.range.restrictScalars ℝ).starProjection_add_starProjection_orthogonal z
  rw [gramColumnProjection_complex_eq_real A hA] at hC
  exact add_left_cancel (hC.trans hR.symm)

end
end JinWishart
#print axioms JinWishart.gramInverseProjector_eq_complex_projection
#print axioms JinWishart.gramColumnProjection_complex_eq_real
#print axioms JinWishart.gramColumnResidualProjection_complex_eq_real
