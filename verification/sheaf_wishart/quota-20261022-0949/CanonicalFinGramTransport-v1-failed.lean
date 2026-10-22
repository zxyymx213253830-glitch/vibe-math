import JinWishartFormalization.CanonicalPhysicalModel

/-! Exact Gram preservation under the canonical Sum row isometry, and a
unit determinant for the Fin square representation of the bijective column
map. Codex. No assertion that the column map is isometric.
[需人工审查] Subsequent positive-spectrum/shear and inverse-moment transport. -/
open Matrix
open scoped BigOperators
namespace JinWishart
noncomputable section

theorem canonicalSumRowAction_gram {m a c : ℕ} {ι : Type*}
    (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin a ⊕ Fin c))
    (X : Matrix (Fin m) ι ℂ) :
    (canonicalSumRowAction V X)ᴴ*(canonicalSumRowAction V X)=Xᴴ*X := by
  ext j k
  have h := V.inner_map_map (WithLp.toLp 2 (fun i => X i j))
    (WithLp.toLp 2 (fun i => X i k))
  simpa only [Matrix.mul_apply,Matrix.conjTranspose_apply,canonicalSumRowAction,
    PiLp.inner_apply,RCLike.inner_apply,Complex.inner,RCLike.star_def,mul_comm] using h

private theorem reindexedColumnLin {n b c : ℕ}
    (T : Matrix (Fin n) (Fin b ⊕ Fin c) ℂ) (e : (Fin b ⊕ Fin c) ≃ Fin n) :
    (T.submatrix id e.symm).toEuclideanLin=T.toEuclideanLin.comp
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).symm.toLinearEquiv.toLinearMap := by
  ext w i
  change (∑ j : Fin n,T i (e.symm j)*w j)=
    ∑ k : Fin b ⊕ Fin c,T i k*w (e k)
  exact Fintype.sum_equiv e.symm _ _ (by intro j; simp)

theorem canonical_reindexed_column_det_isUnit {n b c : ℕ}
    (T : Matrix (Fin n) (Fin b ⊕ Fin c) ℂ)
    (hT : Function.Bijective T.toEuclideanLin) (e : (Fin b ⊕ Fin c) ≃ Fin n) :
    IsUnit (T.submatrix id e.symm).det := by
  have hFin : Function.Injective (T.submatrix id e.symm).toEuclideanLin := by
    rw [reindexedColumnLin]
    exact hT.1.comp (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).symm.injective
  apply Matrix.isUnit_iff_isUnit_det.mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  have hxy' : (T.submatrix id e.symm).toEuclideanLin (WithLp.toLp 2 x)=
      (T.submatrix id e.symm).toEuclideanLin (WithLp.toLp 2 y) :=
    congrArg (WithLp.toLp 2) hxy
  exact congrArg (fun z : EuclideanSpace ℂ (Fin n) => (⇑z)) (hFin hxy')

end
end JinWishart
#print axioms JinWishart.canonicalSumRowAction_gram
#print axioms JinWishart.canonical_reindexed_column_det_isUnit
