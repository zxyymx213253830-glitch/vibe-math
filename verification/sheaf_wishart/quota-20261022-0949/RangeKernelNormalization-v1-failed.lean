import JinWishartFormalization.FixedKernelCompression
import Mathlib.LinearAlgebra.Dimension.LinearMap

/-! Fixed coordinates in which a linear noise factor is an isometry on the
first block and zero on the kernel block. The domain coordinate equivalence
need not be an isometry. Codex. No Gaussian-law preservation by that domain
change is claimed. [需人工审查] Later normal-form/law/model transport. -/
open Module
namespace JinWishart
noncomputable section

theorem exists_linear_range_kernel_normalization
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [FiniteDimensional ℂ F] (T : E →ₗ[ℂ] F) :
    ∃ (b c : ℕ)
      (e : (EuclideanSpace ℂ (Fin b) × EuclideanSpace ℂ (Fin c)) ≃ₗ[ℂ] E)
      (U : EuclideanSpace ℂ (Fin b) →ₗᵢ[ℂ] F),
      b=finrank ℂ T.range ∧ c=finrank ℂ T.ker ∧
      ∀ u v,T (e (u,v))=U u := by
  obtain ⟨g,hg⟩ := T.rangeRestrict.exists_rightInverse_of_surjective T.range_rangeRestrict
  have hTg (y : T.range) : T (g y)=(y : F) :=
    congrArg Subtype.val (LinearMap.congr_fun hg y)
  let L : T.range × T.ker →ₗ[ℂ] E := g.coprod T.ker.subtype
  have hTL (x : T.range × T.ker) : T (L x)=(x.1 : F) := by
    change T (g x.1 + (x.2 : E))=(x.1 : F)
    rw [map_add,hTg]
    have hz : T (x.2 : E)=0 := x.2.property
    rw [hz,add_zero]
  have hbij : Function.Bijective L := by
    constructor
    · intro x y hxy
      have hfst : x.1=y.1 := Subtype.ext (by simpa only [hTL] using congrArg T hxy)
      have hsnd : x.2=y.2 := by
        apply Subtype.ext
        change g x.1+(x.2 : E)=g y.1+(y.2 : E) at hxy
        rw [hfst] at hxy
        exact add_left_cancel hxy
      exact Prod.ext hfst hsnd
    · intro x
      let y : T.range := T.rangeRestrict x
      have hk : x-g y ∈ T.ker := by
        rw [LinearMap.mem_ker,map_sub,hTg]
        exact sub_self _
      refine ⟨(y,⟨x-g y,hk⟩),?_⟩
      change g y+(x-g y)=x
      abel
  let e0 : T.range × T.ker ≃ₗ[ℂ] E := LinearEquiv.ofBijective L hbij
  let b := finrank ℂ T.range
  let c := finrank ℂ T.ker
  let eb : EuclideanSpace ℂ (Fin b) ≃ₗᵢ[ℂ] T.range := (stdOrthonormalBasis ℂ T.range).repr.symm
  let ec : EuclideanSpace ℂ (Fin c) ≃ₗᵢ[ℂ] T.ker := (stdOrthonormalBasis ℂ T.ker).repr.symm
  let e := (LinearEquiv.prodCongr eb.toLinearEquiv ec.toLinearEquiv).trans e0
  let U : EuclideanSpace ℂ (Fin b) →ₗᵢ[ℂ] F := T.range.subtypeₗᵢ.comp eb.toLinearIsometry
  refine ⟨b,c,e,U,rfl,rfl,?_⟩
  intro u v
  exact hTL (eb u,ec v)

end
end JinWishart
#print axioms JinWishart.exists_linear_range_kernel_normalization
