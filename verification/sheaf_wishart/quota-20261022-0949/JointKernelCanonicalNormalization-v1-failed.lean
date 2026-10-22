import JinWishartFormalization.RowSubspaceNormalization

/-! Fixed canonical coordinates for a pair of complex linear maps with
trivial common kernel. Non-isometric column coordinates are kept distinct
from the isometric range frame and row coordinates. Codex.
[需人工审查] Gaussian law/independence and inverse-moment transport. -/
open Module
namespace JinWishart
noncomputable section

theorem exists_joint_kernel_canonical_normalization
    {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [FiniteDimensional ℂ G] (T : E →ₗ[ℂ] F) (M : E →ₗ[ℂ] G)
    (hjoint : Function.Injective (T.prod M)) :
    ∃ (b c a : ℕ)
      (e : (EuclideanSpace ℂ (Fin b) × EuclideanSpace ℂ (Fin c)) ≃ₗ[ℂ] E)
      (U : EuclideanSpace ℂ (Fin b) →ₗᵢ[ℂ] F)
      (V : G ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin a ⊕ Fin c))
      (N : EuclideanSpace ℂ (Fin c) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin c)),
      b=finrank ℂ T.range ∧ c=finrank ℂ T.ker ∧ b+c=finrank ℂ E ∧
      a+c=finrank ℂ G ∧
      (∀ u v,T (e (u,v))=U u) ∧
      ∀ u v,V (M (e (u,v)))=V (M (e (u,0)))+
        WithLp.toLp 2 (Sum.elim (fun _ : Fin a => (0 : ℂ)) (fun j => N v j)) := by
  obtain ⟨b,c,e,U,hb,hc,hT⟩ := exists_linear_range_kernel_normalization T
  let L : EuclideanSpace ℂ (Fin c) →ₗ[ℂ] G :=
    M.comp (e.toLinearMap.comp (LinearMap.inr ℂ (EuclideanSpace ℂ (Fin b))
      (EuclideanSpace ℂ (Fin c))))
  have hL : Function.Injective L := by
    intro x y hxy
    have hx : T (e (0,x))=0 := by simpa using hT 0 x
    have hy : T (e (0,y))=0 := by simpa using hT 0 y
    have he : e (0,x)=e (0,y) := by
      apply hjoint
      exact Prod.ext (hx.trans hy.symm) hxy
    exact congrArg Prod.snd (e.injective he)
  obtain ⟨a,r,V,N,hr,har,hV⟩ := exists_injective_row_subspace_normalization L hL
  have hrc : r=c := by simpa using hr
  subst r
  refine ⟨b,c,a,e,U,V,N,hb,hc,?_,har,hT,?_⟩
  · have hd := e.finrank_eq
    simpa using hd
  · intro u v
    have he : e (u,v)=e (u,0)+e (0,v) := by
      rw [← map_add]
      simp
    rw [he,map_add,map_add]
    exact congrArg (fun z => V (M (e (u,0)))+z) (hV v)

end
end JinWishart
#print axioms JinWishart.exists_joint_kernel_canonical_normalization
