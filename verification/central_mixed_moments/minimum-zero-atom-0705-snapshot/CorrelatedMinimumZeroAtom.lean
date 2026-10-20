import JinWishartFormalization.CorrelatedLogDetGenericRank
import JinWishartFormalization.CorrelatedColumnMinimum
import JinWishartFormalization.CentralWishartCone

/-! Exact zero-atom criterion for the minimum COLUMN Gram eigenvalue.
Codex. Source m-by-p, factor p-by-n, physical mean m-by-n; n>0.
[需人工审查] Inherited null-set/spectral/variance/model correspondence.
No inverse minimum moment criterion is asserted in this singular setting.
-/
open Matrix Module MeasureTheory ProbabilityTheory
open scoped ComplexOrder
namespace JinWishart
noncomputable section

theorem gram_posDef_iff_full_column_rank {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℂ) :
    (complexGram X).PosDef ↔ X.rank=n := by
  rw [(complexGram_posSemidef X).posDef_iff_mulVec_injective]
  change Function.Injective (Xᴴ*X).mulVecLin ↔ X.rank=n
  rw [← LinearMap.ker_eq_bot,Matrix.ker_mulVecLin_conjTranspose_mul_self]
  constructor
  · intro hk
    have hi := LinearMap.finrank_range_of_inj (LinearMap.ker_eq_bot.mp hk)
    simpa only [Matrix.rank,Module.finrank_pi,Fintype.card_fin] using hi
  · intro hr
    have h := X.mulVecLin.finrank_range_add_finrank_ker
    change X.rank+finrank ℂ (LinearMap.ker X.mulVecLin)=finrank ℂ (Fin n → ℂ) at h
    rw [hr,Module.finrank_pi,Fintype.card_fin] at h
    apply Submodule.finrank_eq_zero.mp
    omega

theorem gramSmallestValue_pos_iff_rank {m n : ℕ}
    (X : Matrix (Fin m) (Fin n) ℂ) (hn : 0<n) :
    0<gramSmallestValue X hn ↔ X.rank=n := by
  have h := hermitian_shift_posDef_iff_smallest (complexGram X) (complexGram_posSemidef X).1 hn 0
  have he : (complexGram X).PosDef ↔ 0<gramSmallestValue X hn := by
    simpa only [Complex.ofReal_zero,zero_smul,sub_zero,gramSmallestValue] using h
  rw [← he,gram_posDef_iff_full_column_rank]

theorem gramSmallestValue_zero_iff_rank_lt {m n : ℕ}
    (X : Matrix (Fin m) (Fin n) ℂ) (hn : 0<n) :
    gramSmallestValue X hn=0 ↔ X.rank<n := by
  have hp := gramSmallestValue_pos_iff_rank X hn
  have hb := Matrix.rank_le_width X
  have hn₀ := gramSmallestValue_nonneg X hn
  constructor
  · intro hz
    have he : X.rank≠n := by
      intro hr
      have := hp.mpr hr
      linarith
    omega
  · intro hr
    have he : ¬0<gramSmallestValue X hn := by
      intro hpos
      have := hp.mp hpos
      omega
    exact le_antisymm (le_of_not_gt he) hn₀

theorem actualCorrelatedMinimum_zero_iff_ae {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (hn : 0<n) :
    ∀ᵐ z ∂stdGaussian (ComplexSample (m := m) (n := p)),
      (gramSmallestValue (complexSampleMatrix z*B+M) hn=0 ↔
        min m (Matrix.fromRows B M).rank<n) := by
  filter_upwards [actualCorrelatedRank_eq_generic_ae B M] with z hz
  rw [gramSmallestValue_zero_iff_rank_lt, hz,matrix_fromRows_rank_eq]

theorem actualCorrelatedMinimum_zero_atom {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (hn : 0<n) :
    (stdGaussian (ComplexSample (m := m) (n := p))).real
      {z | gramSmallestValue (complexSampleMatrix z*B+M) hn=0} =
      if min m (Matrix.fromRows B M).rank<n then 1 else 0 := by
  classical
  let μ := stdGaussian (ComplexSample (m := m) (n := p))
  have ha := actualCorrelatedMinimum_zero_iff_ae B M hn
  by_cases hq : min m (Matrix.fromRows B M).rank<n
  · rw [if_pos hq]
    have he : {z | gramSmallestValue (complexSampleMatrix z*B+M) hn=0} =ᵐ[μ] Set.univ := by
      filter_upwards [ha] with z hz
      exact propext (by simpa only [Set.mem_setOf_eq,Set.mem_univ,iff_true] using hz.mpr hq)
    change μ.real _=1
    rw [measureReal_def,measure_congr he]
    simp [μ]
  · rw [if_neg hq]
    have he : {z | gramSmallestValue (complexSampleMatrix z*B+M) hn=0} =ᵐ[μ] ∅ := by
      filter_upwards [ha] with z hz
      apply propext
      simpa only [Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false] using mt hz.mp hq
    change μ.real _=0
    rw [measureReal_def,measure_congr he]
    simp

end
end JinWishart
#print axioms JinWishart.gram_posDef_iff_full_column_rank
#print axioms JinWishart.gramSmallestValue_pos_iff_rank
#print axioms JinWishart.gramSmallestValue_zero_iff_rank_lt
#print axioms JinWishart.actualCorrelatedMinimum_zero_iff_ae
#print axioms JinWishart.actualCorrelatedMinimum_zero_atom
