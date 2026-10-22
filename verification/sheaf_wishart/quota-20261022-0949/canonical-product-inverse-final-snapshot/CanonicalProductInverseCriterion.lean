import JinWishartFormalization.CanonicalBlockRank

/-! Candidate assembly of the canonical product-Gaussian inverse criterion.
[需人工审查] Product law, AE full rank and inverse-moment transport.
Controls reused before source: Fin block299, rank193, factor591, product42.
This file is not accepted until all exact checks/review/audit pass. -/
open Matrix Module MeasureTheory ProbabilityTheory
open scoped ComplexOrder
namespace JinWishart
noncomputable section

private theorem iidRank_ae {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℂ) :
    ∀ᵐ z ∂stdGaussian (ComplexSample (m := a) (n := b)),
      (complexSampleMatrix z+M).rank=min a b := by
  have hr := actualCorrelatedRank_eq_generic_ae (1 : Matrix (Fin b) (Fin b) ℂ) M
  have hk : LinearMap.ker (1 : Matrix (Fin b) (Fin b) ℂ).mulVecLin=⊥ := by
    rw [Matrix.mulVecLin_one,LinearMap.ker_id]
  have hd : finrank ℂ (M.mulVecLin.domRestrict (LinearMap.ker
      (1 : Matrix (Fin b) (Fin b) ℂ).mulVecLin)).range=0 := by
    rw [LinearMap.range_domRestrict,hk,Submodule.map_bot,finrank_bot]
  simpa only [Matrix.mul_one,Matrix.rank_one,Fintype.card_fin,hd,Nat.add_zero] using hr

private theorem inverseMinIntegrable {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ) (hf : Measurable f)
    (hpos : ∀ᵐ x ∂μ,0<f x) (t p : ℝ) (ht : 0<t) (hp : 0<p) :
    Integrable (fun x => (min (f x) t)⁻¹^p) μ ↔ Integrable (fun x => (f x)⁻¹^p) μ := by
  constructor
  · intro h
    apply h.mono' (hf.inv.pow_const p).aestronglyMeasurable
    filter_upwards [hpos] with x hx
    change |(f x)⁻¹^p|≤(min (f x) t)⁻¹^p
    rw [abs_of_nonneg (Real.rpow_nonneg (inv_nonneg.mpr hx.le) p)]
    apply Real.rpow_le_rpow (inv_nonneg.mpr hx.le) _ hp.le
    simpa only [one_div] using one_div_le_one_div_of_le (lt_min hx ht) (min_le_left _ _)
  · intro h
    apply (h.add (integrable_const (t⁻¹^p))).mono'
      ((hf.min measurable_const).inv.pow_const p).aestronglyMeasurable
    filter_upwards [hpos] with x hx
    change |(min (f x) t)⁻¹^p|≤(f x)⁻¹^p+t⁻¹^p
    rw [abs_of_nonneg (Real.rpow_nonneg (inv_nonneg.mpr (le_min hx.le ht.le)) p)]
    by_cases hxt : f x≤t
    · rw [min_eq_left hxt]
      exact le_add_of_nonneg_right (Real.rpow_nonneg (inv_nonneg.mpr ht.le) p)
    · rw [min_eq_right (le_of_not_ge hxt)]
      exact le_add_of_nonneg_left (Real.rpow_nonneg (inv_nonneg.mpr hx.le) p)

private theorem iidPositiveInverseCriterion {a b : ℕ} (ha : 0<a) (hb : 0<b)
    (M : Matrix (Fin a) (Fin b) ℂ) (j : Fin (Fintype.card (Fin b)))
    (hj : j.val+1=min a b) (p : ℝ) (hp : 0<p) :
    Integrable (fun z => (complexNoncentralSampleEigenvalue M j z)⁻¹^p)
      (stdGaussian (ComplexSample (m := a) (n := b))) ↔
        p<((max a b-min a b+1 : ℕ) : ℝ) := by
  by_cases hba : b≤a
  · have he : j=smallestEigenvalue₀Index hb := by
      have hlast : (smallestEigenvalue₀Index hb).val+1=b := by
        simp [smallestEigenvalue₀Index,Fintype.card_fin]
        omega
      apply Fin.ext
      rw [Nat.min_eq_right hba] at hj
      omega
    rw [he,Nat.max_eq_left hba,Nat.min_eq_right hba]
    exact actualNoncentralRectangular_inverseMinimum_realMoment_integrable_iff a b hb hba M p hp
  · have hab : a≤b := by omega
    rw [Nat.max_eq_right hab,Nat.min_eq_left hab]
    exact actualWide_fixed_positive_inverse_realMoment_integrable_iff a b ha hab M j
      (hj.trans (Nat.min_eq_left hab)) p hp

theorem canonical_product_inverse_realMoment_integrable_iff {a b c m n : ℕ}
    (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (er : (Fin a ⊕ Fin c) ≃ Fin m) (ec : (Fin b ⊕ Fin c) ≃ Fin n)
    (MA : Matrix (Fin a) (Fin b) ℂ) (MH : Matrix (Fin c) (Fin b) ℂ)
    (N : Matrix (Fin c) (Fin c) ℂ) (hN : IsUnit N.det)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=min m n)
    (j : Fin (Fintype.card (Fin b))) (hj : j.val+1=min a b)
    (k : Fin (Fintype.card (Fin c))) (hk : k.val+1=c)
    (p : ℝ) (hp : 0<p) :
    Integrable (fun w : ComplexSample (m := a) (n := b) × ComplexSample (m := c) (n := b) =>
      ((complexGram_posSemidef (canonicalFinBlock er ec (complexSampleMatrix w.1+MA)
        (complexSampleMatrix w.2+MH) N)).1.eigenvalues₀ i)⁻¹^p)
      ((stdGaussian (ComplexSample (m := a) (n := b))).prod
        (stdGaussian (ComplexSample (m := c) (n := b)))) ↔
      p<((max a b-min a b+1 : ℕ) : ℝ) := by
  classical
  let μ := stdGaussian (ComplexSample (m := a) (n := b))
  let ν := stdGaussian (ComplexSample (m := c) (n := b))
  let A (z : ComplexSample (m := a) (n := b)) := complexSampleMatrix z+MA
  let H (z : ComplexSample (m := c) (n := b)) := complexSampleMatrix z+MH
  let D (w : ComplexSample (m := a) (n := b) × ComplexSample (m := c) (n := b)) :=
    canonicalFinBlock er ec (A w.1) (H w.2) N
  let f (w : ComplexSample (m := a) (n := b) × ComplexSample (m := c) (n := b)) :=
    (complexGram_posSemidef (D w)).1.eigenvalues₀ i
  let t := (complexGram_posSemidef N).1.eigenvalues₀ k
  let g (z : ComplexSample (m := a) (n := b)) := min (complexNoncentralSampleEigenvalue MA j z) t
  let K (z : ComplexSample (m := c) (n := b)) :=
    (1+‖(Matrix.toEuclideanLin (N⁻¹*H z)).toContinuousLinearMap‖)^2
  have hmn : a+c=m := by simpa using Fintype.card_congr er
  have hnn : b+c=n := by simpa using Fintype.card_congr ec
  have hm : 0<m := by omega
  have hn : 0<n := by omega
  have hNr : N.rank=c := by simpa only [Fintype.card_fin] using Matrix.rank_of_det_ne_zero hN.ne_zero
  have hNmin := antitone_min_positive_at_count _ (complexGram_posSemidef N).1.eigenvalues₀_antitone
    k ((gram_positive_modes_card_eq_rank N).trans (hNr.trans hk.symm))
  have hAr := iidRank_ae MA
  have hAp : ∀ᵐ z ∂μ,0<complexNoncentralSampleEigenvalue MA j z := by
    filter_upwards [hAr] with z hz
    exact (antitone_min_positive_at_count _ (complexGram_posSemidef (A z)).1.eigenvalues₀_antitone
      j ((gram_positive_modes_card_eq_rank (A z)).trans (hz.trans hj.symm))).1
  have hfm : Measurable f := by
    have hX (u : Fin m) (v : Fin n) : Measurable (fun w => D w u v) := by
      dsimp only [D,canonicalFinBlock,Matrix.coe_reindexLinearEquiv,Matrix.reindex_apply,
        Matrix.submatrix_apply]
      rcases er.symm u with u|u <;> rcases ec.symm v with v|v <;>
        simp only [Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
          Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,A,H,Matrix.add_apply,complexSampleMatrix] <;> fun_prop
    have hG : Measurable (fun w => complexGram (D w)) := by
      apply Measurable.of_eval
      intro u
      apply Measurable.of_eval
      intro v
      simp only [complexGram,Matrix.mul_apply,Matrix.conjTranspose_apply]
      apply Finset.measurable_sum
      intro l _
      simpa only [RCLike.star_def,Function.comp_apply,Pi.mul_apply] using!
        (Complex.continuous_conj.measurable.comp (hX l u)).mul (hX l v)
    change Measurable ((fun Q : HermitianMatrix n => hermitianEigenvalueVector Q i) ∘
      fun w => (⟨complexGram (D w),(complexGram_posSemidef (D w)).1⟩ : HermitianMatrix n))
    exact ((orderedHermitianEigenvalueCoordinatesContinuous n i).measurable).comp
      (hG.subtype_mk (h := fun w => (complexGram_posSemidef (D w)).1))
  have hgm : Measurable g := (measurable_actualNoncentralEigenvalue MA j).min measurable_const
  have hKpos (z) : 0<K z := by dsimp [K];positivity
  have hKI : Integrable (fun z => (K z)^p) ν := by
    have hh := integrable_actual_canonical_shear_factor N⁻¹ MH (2*p) (by positivity)
    convert hh using 1
    funext z
    exact (Real.rpow_natCast_mul (by positivity) 2 p).symm
  have hbnd : ∀ᵐ w ∂μ.prod ν,0<f w ∧ 0<g w.1 ∧ g w.1≤K w.2*f w ∧ f w≤K w.2*g w.1 := by
    filter_upwards [(measurePreserving_fst (μ := μ) (ν := ν)).quasiMeasurePreserving.ae hAr] with w hw
    have hminA := antitone_min_positive_at_count _ (complexGram_posSemidef (A w.1)).1.eigenvalues₀_antitone
      j ((gram_positive_modes_card_eq_rank (A w.1)).trans (hw.trans hj.symm))
    have hsolve : N*(N⁻¹*H w.2)=H w.2 := by rw [← Matrix.mul_assoc,Matrix.mul_nonsing_inv _ hN,Matrix.one_mul]
    have hrD : (D w).rank=min m n := by
      rw [canonical_fin_block_rank er ec _ _ N hN,hw]
      omega
    exact canonical_fin_block_minimum_bounds er ec (A w.1) (H w.2) (N⁻¹*H w.2) N hsolve
      hm hn hrD i hi j k hminA.1 hNmin.1 hminA.2 hNmin.2
  have ht : 0<t := hNmin.1
  exact (integrable_inverse_rpow_iff_of_separable_comparison μ ν f g K hfm hgm hKpos p hp hKI hbnd).trans
    ((inverseMinIntegrable μ (complexNoncentralSampleEigenvalue MA j)
      (measurable_actualNoncentralEigenvalue MA j) hAp t p ht hp).trans
        (iidPositiveInverseCriterion ha hb MA j hj p hp))

end
end JinWishart
#print axioms JinWishart.canonical_product_inverse_realMoment_integrable_iff
