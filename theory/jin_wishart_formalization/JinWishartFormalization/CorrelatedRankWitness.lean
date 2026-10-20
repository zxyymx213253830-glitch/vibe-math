import JinWishartFormalization.CorrelatedRankUpperBound
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dimension.Free

/-! Deterministic maximal affine rank, including singular rectangular factors.
Codex. Pure linear algebra; no almost-sure statement.
[需人工审查] Rank/model correspondence. The mean is explicitly subtracted in the witness.
-/
open Matrix Module
namespace JinWishart
noncomputable section
variable {V U W : Type*} [AddCommGroup V] [AddCommGroup U] [AddCommGroup W]
  [Module ℂ V] [Module ℂ U] [Module ℂ W]
  [Module.Finite ℂ V] [Module.Finite ℂ U] [Module.Finite ℂ W]

theorem exists_linearMap_maximal_rank :
    ∃ f : U →ₗ[ℂ] W, finrank ℂ (LinearMap.range f) = min (finrank ℂ U) (finrank ℂ W) := by
  by_cases h : finrank ℂ U ≤ finrank ℂ W
  · obtain ⟨f,hf⟩ := (finrank_le_iff_exists_linearMap (R := ℂ) (M := U) (M' := W)).mp h
    exact ⟨f,by rw [LinearMap.finrank_range_of_inj hf,min_eq_left h]⟩
  · obtain ⟨g,hg⟩ := (finrank_le_iff_exists_linearMap (R := ℂ) (M := W) (M' := U)).mp (le_of_not_ge h)
    obtain ⟨f,hf⟩ := g.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hg)
    have hs : Function.Surjective f := by
      intro w
      exact ⟨g w,LinearMap.congr_fun hf w⟩
    exact ⟨f,by rw [LinearMap.range_eq_top.mpr hs,finrank_top,min_eq_right (le_of_not_ge h)]⟩

theorem exists_linearMap_affine_comp_maximal_rank (b : V →ₗ[ℂ] U) (a : V →ₗ[ℂ] W) :
    ∃ z : U →ₗ[ℂ] W, finrank ℂ (LinearMap.range (z.comp b+a)) =
      min (finrank ℂ W) (finrank ℂ (LinearMap.range b) +
        finrank ℂ (LinearMap.range (a.domRestrict (LinearMap.ker b)))) := by
  classical
  let K := LinearMap.ker b
  obtain ⟨C,hKC⟩ := K.exists_isCompl
  let e : C ≃ₗ[ℂ] LinearMap.range b := b.kerComplementEquivRange hKC.symm
  let R := LinearMap.range (a.domRestrict K)
  obtain ⟨D,hRD⟩ := R.exists_isCompl
  obtain ⟨g,hg⟩ := exists_linearMap_maximal_rank (U := C) (W := D)
  let ψ := D.subtype.comp g
  let f := LinearMap.ofIsCompl hKC (a.domRestrict K) ψ
  let t : LinearMap.range b →ₗ[ℂ] W := (ψ-a.domRestrict C).comp e.symm.toLinearMap
  obtain ⟨z,hz⟩ := t.exists_extend
  have hc (c : C) : z (b c)=ψ c-a c := by
    have ht := LinearMap.congr_fun hz (e c)
    have hec : (e c : U)=b c := rfl
    change z (e c : U)=t (e c) at ht
    rw [hec] at ht
    simpa only [LinearMap.comp_apply,t,LinearMap.sub_apply,LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply,LinearMap.domRestrict_apply,
      Submodule.coe_subtype] using ht
  have hf : f=z.comp b+a := by
    apply LinearMap.ofIsCompl_eq hKC
    · intro k
      change a k=z (b k)+a k
      rw [k.property,map_zero,zero_add]
    · intro c
      change ψ c=z (b c)+a c
      rw [hc,sub_add_cancel]
  have hd : finrank ℂ (LinearMap.range ψ) = finrank ℂ (LinearMap.range g) := by
    rw [LinearMap.range_comp,Submodule.finrank_map_subtype_eq]
  have hle : LinearMap.range ψ ≤ D := by
    rintro _ ⟨c,rfl⟩
    exact (g c).property
  have hdis : Disjoint R (LinearMap.range ψ) := hRD.disjoint.mono_right hle
  have hs := Submodule.finrank_sup_add_finrank_inf_eq R (LinearMap.range ψ)
  rw [hdis.eq_bot,finrank_bot,add_zero,hd,hg] at hs
  have hC : finrank ℂ C = finrank ℂ (LinearMap.range b) := e.finrank_eq
  have hD : finrank ℂ R+finrank ℂ D=finrank ℂ W := Submodule.finrank_add_eq_of_isCompl hRD
  refine ⟨z,?_⟩
  rw [← hf,LinearMap.range_ofIsCompl]
  change finrank ℂ (R ⊔ LinearMap.range ψ : Submodule ℂ W) = _
  rw [hs,hC]
  change finrank ℂ R + min (finrank ℂ (LinearMap.range b)) (finrank ℂ D) =
    min (finrank ℂ W) (finrank ℂ (LinearMap.range b)+finrank ℂ R)
  omega

end
end JinWishart
#print axioms JinWishart.exists_linearMap_maximal_rank
#print axioms JinWishart.exists_linearMap_affine_comp_maximal_rank
