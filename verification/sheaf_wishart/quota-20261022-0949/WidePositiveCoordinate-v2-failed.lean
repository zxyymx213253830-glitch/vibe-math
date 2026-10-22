import JinWishartFormalization.WideRowInverseMoments
import JinWishartFormalization.GramPositiveSpectrumTransport
import JinWishartFormalization.GaussianGramLogMoments

/-! Fixed column-Gram coordinate at the positive rank boundary in a wide IID
model. It is not the last column coordinate when n>m. Codex.
[需人工审查] Inherited AE rank, real powers, source/law transport and model. -/
open Matrix MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

private theorem members {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℂ) (x : ℝ) (hx : 0<x) :
    (∃ i,(complexGram_posSemidef X).1.eigenvalues₀ i=x) ↔
      ∃ j,(complexGram_posSemidef Xᴴ).1.eigenvalues₀ j=x := by
  have hxC : (x : ℂ)≠0 := by exact_mod_cast hx.ne'
  rw [← hermitian_real_root_iff_ordered_eigenvalue,
    gram_nonzero_root_mem_iff_conjTranspose X _ hxC,
    hermitian_real_root_iff_ordered_eigenvalue]

theorem gram_full_row_rank_coordinate_eq_rowMinimum {m n : ℕ}
    (X : Matrix (Fin m) (Fin n) ℂ) (hm : 0<m)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=m) (hr : X.rank=m) :
    0<(complexGram_posSemidef X).1.eigenvalues₀ i ∧
      (complexGram_posSemidef X).1.eigenvalues₀ i=gramSmallestValue Xᴴ hm := by
  classical
  have hcount := (gram_positive_modes_card_eq_rank X).trans (hr.trans hi.symm)
  have hmin := antitone_min_positive_at_count _ (complexGram_posSemidef X).1.eigenvalues₀_antitone i hcount
  let j := smallestEigenvalue₀Index hm
  have hj : j.val+1=m := by
    simp [j,smallestEigenvalue₀Index,Fintype.card_fin]
    omega
  have hcount' := (gram_positive_modes_card_eq_rank Xᴴ).trans
    ((Matrix.rank_conjTranspose X).trans (hr.trans hj.symm))
  have hmin' := antitone_min_positive_at_count _ (complexGram_posSemidef Xᴴ).1.eigenvalues₀_antitone j hcount'
  refine ⟨hmin.1,le_antisymm ?_ ?_⟩
  · obtain ⟨k,hk⟩ := (members X _ hmin'.1).mpr ⟨j,rfl⟩
    exact (hmin.2 k (by rw [hk];exact hmin'.1)).trans_eq hk
  · obtain ⟨k,hk⟩ := (members X _ hmin.1).mp ⟨i,rfl⟩
    exact (hmin'.2 k (by rw [hk];exact hmin.1)).trans_eq hk

theorem actualWide_fixed_positive_coordinate_ae (m n : ℕ) (hm : 0<m) (hmn : m≤n)
    (M : Matrix (Fin m) (Fin n) ℂ) (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=m) :
    ∀ᵐ z ∂stdGaussian (ComplexSample (m := m) (n := n)),
      0<complexNoncentralSampleEigenvalue M i z ∧
      complexNoncentralSampleEigenvalue M i z=gramSmallestValue (complexSampleMatrix z+M)ᴴ hm := by
  have hr := actualCorrelatedRank_eq_generic_ae (1 : Matrix (Fin n) (Fin n) ℂ) M
  have hker : LinearMap.ker (1 : Matrix (Fin n) (Fin n) ℂ).mulVecLin=⊥ := by
    rw [Matrix.mulVecLin_one,LinearMap.ker_id]
  simp [hker,LinearMap.range_domRestrict,Nat.min_eq_left hmn] at hr
  filter_upwards [hr] with z hz
  exact gram_full_row_rank_coordinate_eq_rowMinimum _ hm i hi hz

theorem actualWide_fixed_positive_inverse_realMoment_integrable_iff (m n : ℕ)
    (hm : 0<m) (hmn : m≤n) (M : Matrix (Fin m) (Fin n) ℂ)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=m) (p : ℝ) (hp : 0<p) :
    Integrable (fun z => ((complexNoncentralSampleEigenvalue M i z)⁻¹)^p)
      (stdGaussian (ComplexSample (m := m) (n := n))) ↔ p<((n-m+1 : ℕ) : ℝ) := by
  have he : (fun z => ((complexNoncentralSampleEigenvalue M i z)⁻¹)^p) =ᵐ[stdGaussian _]
      (fun z => ((gramSmallestValue (complexSampleMatrix z+M)ᴴ hm)⁻¹)^p) := by
    filter_upwards [actualWide_fixed_positive_coordinate_ae m n hm hmn M i hi] with z hz
    rw [hz.2]
  have hF : Measurable (fun X : Matrix (Fin m) (Fin n) ℂ => ((gramSmallestValue Xᴴ hm)⁻¹)^p) :=
    ((measurable_gramSmallestValue hm).comp (by fun_prop)).inv.pow_const p
  have h := wideRowMinimum_inverse_realMoment_integrable_iff m n hm hmn M p hp
  unfold complexGaussianMatrixLaw at h
  rw [integrable_map_measure hF.aestronglyMeasurable
    (measurable_shiftedComplexSampleMatrix M).aemeasurable] at h
  exact (integrable_congr he).trans h

theorem actualWide_fixed_positive_inverse_realMoment_lintegral_eq_top (m n : ℕ)
    (hm : 0<m) (hmn : m≤n) (M : Matrix (Fin m) (Fin n) ℂ)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=m)
    (p : ℝ) (hp : ((n-m+1 : ℕ) : ℝ)≤p) :
    (∫⁻ z,ENNReal.ofReal (((complexNoncentralSampleEigenvalue M i z)⁻¹)^p)
      ∂stdGaussian (ComplexSample (m := m) (n := n)))=⊤ := by
  have hp0 : 0<p := lt_of_lt_of_le (by positivity : (0 : ℝ)<((n-m+1 : ℕ) : ℝ)) hp
  have hF := (measurable_actualNoncentralEigenvalue M i).inv.pow_const p
  by_contra h
  have hi' := (lintegral_ofReal_ne_top_iff_integrable hF.aestronglyMeasurable
    (ae_of_all _ (fun z => Real.rpow_nonneg
      (inv_nonneg.mpr (complexNoncentralGram_eigenvalues₀_nonneg M z i)) p))).mp h
  exact (not_lt_of_ge hp)
    ((actualWide_fixed_positive_inverse_realMoment_integrable_iff m n hm hmn M i hi p hp0).mp hi')

end
end JinWishart
#print axioms JinWishart.gram_full_row_rank_coordinate_eq_rowMinimum
#print axioms JinWishart.actualWide_fixed_positive_coordinate_ae
#print axioms JinWishart.actualWide_fixed_positive_inverse_realMoment_integrable_iff
#print axioms JinWishart.actualWide_fixed_positive_inverse_realMoment_lintegral_eq_top
