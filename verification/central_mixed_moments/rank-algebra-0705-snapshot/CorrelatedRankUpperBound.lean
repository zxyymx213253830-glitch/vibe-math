import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Basic.Complex.Basic

/-! Deterministic rank obstruction for arbitrary fixed rectangular factors.
Codex. No generic rank attainment or Gaussian assertion is made here.
[需人工审查] Matrix/linear map/model correspondence.
-/
open Matrix Module
namespace JinWishart
noncomputable section

variable {V U W : Type*} [AddCommGroup V] [AddCommGroup U] [AddCommGroup W]
  [Module ℂ V] [Module ℂ U] [Module ℂ W]
  [Module.Finite ℂ V] [Module.Finite ℂ U] [Module.Finite ℂ W]

theorem linearMap_pair_rank (b : V →ₗ[ℂ] U) (a : V →ₗ[ℂ] W) :
    finrank ℂ (LinearMap.range (b.prod a)) =
      finrank ℂ (LinearMap.range b) +
        finrank ℂ (LinearMap.range (a.domRestrict (LinearMap.ker b))) := by
  let K := LinearMap.ker b
  have he : (LinearMap.ker (a.domRestrict K)).map K.subtype =
      LinearMap.ker (b.prod a) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      change (b y.val,a y.val) = 0
      exact Prod.ext y.property hy
    · intro hx
      have hb : b x=0 := congrArg Prod.fst hx
      have ha : a x=0 := congrArg Prod.snd hx
      exact ⟨⟨x,hb⟩,ha,rfl⟩
  have hd : finrank ℂ (LinearMap.ker (a.domRestrict K)) =
      finrank ℂ (LinearMap.ker (b.prod a)) := by
    rw [← he,Submodule.finrank_map_subtype_eq]
  have h₁ := b.finrank_range_add_finrank_ker
  have h₂ := (a.domRestrict K).finrank_range_add_finrank_ker
  have h₃ := (b.prod a).finrank_range_add_finrank_ker
  change finrank ℂ (LinearMap.range b) + finrank ℂ K = finrank ℂ V at h₁
  dsimp only [K] at h₁ h₂ hd
  omega

theorem linearMap_affine_comp_rank_le (b : V →ₗ[ℂ] U) (a : V →ₗ[ℂ] W)
    (z : U →ₗ[ℂ] W) :
    finrank ℂ (LinearMap.range (z.comp b+a)) ≤
      min (finrank ℂ W) (finrank ℂ (LinearMap.range b) +
        finrank ℂ (LinearMap.range (a.domRestrict (LinearMap.ker b)))) := by
  have hk : LinearMap.ker (b.prod a) ≤ LinearMap.ker (z.comp b+a) := by
    intro x hx
    have hb : b x=0 := congrArg Prod.fst hx
    have ha : a x=0 := congrArg Prod.snd hx
    change z (b x)+a x=0
    simp [hb,ha]
  have hd := Submodule.finrank_mono hk
  have h₁ := (b.prod a).finrank_range_add_finrank_ker
  have h₂ := (z.comp b+a).finrank_range_add_finrank_ker
  have he := linearMap_pair_rank b a
  refine le_min (Submodule.finrank_le _) ?_
  omega

theorem matrix_affine_comp_rank_le {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (Z : Matrix (Fin m) (Fin p) ℂ) :
    (Z*B+M).rank ≤ min m (B.rank +
      finrank ℂ (LinearMap.range (M.mulVecLin.domRestrict (LinearMap.ker B.mulVecLin)))) := by
  change finrank ℂ (LinearMap.range (Z*B+M).mulVecLin) ≤ _
  rw [Matrix.mulVecLin_add,Matrix.mulVecLin_mul]
  simpa only [Matrix.rank,Module.finrank_pi,Fintype.card_fin] using
    linearMap_affine_comp_rank_le B.mulVecLin M.mulVecLin Z.mulVecLin

end
end JinWishart
#print axioms JinWishart.linearMap_pair_rank
#print axioms JinWishart.linearMap_affine_comp_rank_le
#print axioms JinWishart.matrix_affine_comp_rank_le
