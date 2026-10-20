import JinWishartFormalization.CorrelatedRankUpperBound
import JinWishartFormalization.GramMinimumColumnComparison
import Mathlib.LinearAlgebra.Dimension.Free

/-! Fixed noiseless mean directions can enforce a uniform ROW Gram spectral gap.
Codex. The fixed-right-inverse criterion is deterministic, for every noise Z.
[需人工审查] Operator/spectral and physical-model correspondence.
No general singular-model inverse-moment threshold is claimed.
-/
open Matrix Module
namespace JinWishart
noncomputable section

theorem exists_noiseless_right_inverse {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (hs : finrank ℂ (LinearMap.range (M.mulVecLin.domRestrict (LinearMap.ker B.mulVecLin)))=m) :
    ∃ C : Matrix (Fin n) (Fin m) ℂ, B*C=0 ∧ M*C=1 := by
  classical
  let K := LinearMap.ker B.mulVecLin
  let a := M.mulVecLin.domRestrict K
  have ha : LinearMap.range a=⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simpa only [Module.finrank_pi,Fintype.card_fin] using hs
  obtain ⟨s,hs⟩ := a.exists_rightInverse_of_surjective ha
  let c := K.subtype.comp s
  have hb : B.mulVecLin.comp c=0 := by
    apply LinearMap.ext
    intro v
    exact (s v).property
  have hm : M.mulVecLin.comp c=LinearMap.id := hs
  refine ⟨LinearMap.toMatrix' c,?_,?_⟩
  · have h := congrArg LinearMap.toMatrix' hb
    simpa only [LinearMap.toMatrix'_comp,← Matrix.toLin'_apply',
      LinearMap.toMatrix'_toLin',map_zero] using h
  · have h := congrArg LinearMap.toMatrix' hm
    simpa only [LinearMap.toMatrix'_comp,← Matrix.toLin'_apply',
      LinearMap.toMatrix'_toLin',LinearMap.toMatrix'_id] using h

def noiselessRightInverseControl {m n : ℕ} (C : Matrix (Fin n) (Fin m) ℂ) : ℝ :=
  max 1 (‖LinearMap.toContinuousLinearMap ((Cᴴ).toEuclideanLin)‖^2)

theorem noiselessRightInverseControl_pos {m n : ℕ} (C : Matrix (Fin n) (Fin m) ℂ) :
    0<noiselessRightInverseControl C :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ)<1) (le_max_left _ _)

theorem rowGram_minimum_lower_of_right_inverse {m n : ℕ}
    (X : Matrix (Fin m) (Fin n) ℂ) (C : Matrix (Fin n) (Fin m) ℂ)
    (hXC : X*C=1) (hm : 0<m) :
    1/noiselessRightInverseControl C ≤ gramSmallestValue Xᴴ hm := by
  obtain ⟨u,hu,he⟩ := exists_gram_minimum_unit_vector Xᴴ hm
  have hi : LinearMap.toContinuousLinearMap ((Cᴴ).toEuclideanLin) ((Xᴴ).toEuclideanLin u)=u := by
    ext i
    change (Cᴴ *ᵥ (Xᴴ *ᵥ ⇑u)) i=u i
    rw [Matrix.mulVec_mulVec,← Matrix.conjTranspose_mul,hXC,Matrix.conjTranspose_one,Matrix.one_mulVec]
  have hb := pow_le_pow_left₀ (norm_nonneg (LinearMap.toContinuousLinearMap ((Cᴴ).toEuclideanLin)
      ((Xᴴ).toEuclideanLin u)))
    ((LinearMap.toContinuousLinearMap ((Cᴴ).toEuclideanLin)).le_opNorm ((Xᴴ).toEuclideanLin u)) 2
  rw [hi,hu,one_pow,mul_pow,he] at hb
  have hc : ‖LinearMap.toContinuousLinearMap ((Cᴴ).toEuclideanLin)‖^2 ≤ noiselessRightInverseControl C :=
    le_max_right _ _
  have hn := gramSmallestValue_nonneg Xᴴ hm
  have hp := noiselessRightInverseControl_pos C
  apply (div_le_iff₀ hp).mpr
  nlinarith

theorem correlated_rowGram_uniform_floor {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (hm : 0<m)
    (hs : finrank ℂ (LinearMap.range (M.mulVecLin.domRestrict (LinearMap.ker B.mulVecLin)))=m) :
    ∃ δ : ℝ, 0<δ ∧ ∀ Z : Matrix (Fin m) (Fin p) ℂ,
      δ ≤ gramSmallestValue (Z*B+M)ᴴ hm := by
  obtain ⟨C,hBC,hMC⟩ := exists_noiseless_right_inverse B M hs
  refine ⟨1/noiselessRightInverseControl C,one_div_pos.mpr (noiselessRightInverseControl_pos C),?_⟩
  intro Z
  apply rowGram_minimum_lower_of_right_inverse _ C _ hm
  rw [Matrix.add_mul,Matrix.mul_assoc,hBC,Matrix.mul_zero,zero_add,hMC]

end
end JinWishart
#print axioms JinWishart.exists_noiseless_right_inverse
#print axioms JinWishart.noiselessRightInverseControl_pos
#print axioms JinWishart.rowGram_minimum_lower_of_right_inverse
#print axioms JinWishart.correlated_rowGram_uniform_floor
