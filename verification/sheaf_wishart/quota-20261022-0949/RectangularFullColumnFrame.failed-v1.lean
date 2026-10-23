import JinWishartFormalization.ActualSingularInverseEdges

/-! Fixed full-column-rank rectangular noise factor normalized by an
invertible column matrix. Existence, not an executable QR algorithm. Codex.
Controls seed2026102238:18 exact cases/109 checks before source.
[需人工审查] Subsequent original-source Gaussian and inverse transport. -/
open Matrix Module
namespace JinWishart
noncomputable section

theorem exists_rectangular_full_column_frame {p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (hB : B.rank=n) :
    ∃ (S : Matrix (Fin n) (Fin n) ℂ) (U : Matrix (Fin p) (Fin n) ℂ),
      IsUnit S.det ∧ Uᴴ*U=1 ∧ B*S=U := by
  have hrange : B.rank=finrank ℂ B.toEuclideanLin.range := by
    convert! B.rank_eq_finrank_range_toLin
      (EuclideanSpace.basisFun (Fin p) ℂ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℂ).toBasis using 1
  have hk : finrank ℂ B.toEuclideanLin.ker=0 := by
    have hd := B.toEuclideanLin.finrank_range_add_finrank_ker
    rw [← hrange,hB] at hd
    simp only [finrank_euclideanSpace_fin] at hd
    omega
  have hinj : Function.Injective B.toEuclideanLin :=
    LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hk)
  have hjoint : Function.Injective (B.toEuclideanLin.prod
      (0 : Matrix (Fin 0) (Fin n) ℂ).toEuclideanLin) := by
    intro x y hh
    exact hinj (congrArg Prod.fst hh)
  obtain ⟨b,c,a,T,U,V,N,MA,MH,hb,hc,hbc,hac,hT,hU,hBT,hN,hMean⟩ :=
    exists_joint_kernel_canonical_matrix B (0 : Matrix (Fin 0) (Fin n) ℂ) hjoint
  have hc0 : c=0 := by omega
  subst c
  have hbn : b=n := by omega
  clear hb
  subst b
  let ec : (Fin n ⊕ Fin 0) ≃ Fin n := Equiv.sumEmpty _ _
  let S : Matrix (Fin n) (Fin n) ℂ := T.submatrix id ec.symm
  refine ⟨S,U,canonical_reindexed_column_det_isUnit T hT ec,hU,?_⟩
  ext i j
  change (B*T) i (Sum.inl j)=U i j
  rw [hBT]
  rfl

end
end JinWishart
#print axioms JinWishart.exists_rectangular_full_column_frame
