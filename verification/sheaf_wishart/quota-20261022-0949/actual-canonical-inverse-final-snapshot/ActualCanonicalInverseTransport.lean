import JinWishartFormalization.CanonicalMatrixProductInverse

/-! Physical-source inverse threshold under explicit fixed canonical data.
Controls reused before source: physical Fin130, block299, factor591, product42.
[需人工审查] Actual source/variance, AE comparisons and matrix-law pushforwards.
This is not yet the existence/edge-branch assembly for arbitrary singular B. -/
open Matrix MeasureTheory ProbabilityTheory
open scoped ComplexOrder
namespace JinWishart
noncomputable section

private theorem measurableCoordinate {a b c m n : ℕ}
    (er : (Fin a ⊕ Fin c) ≃ Fin m) (ec : (Fin b ⊕ Fin c) ≃ Fin n)
    (N : Matrix (Fin c) (Fin c) ℂ) (i : Fin (Fintype.card (Fin n))) :
    Measurable (fun w : Matrix (Fin a) (Fin b) ℂ × Matrix (Fin c) (Fin b) ℂ =>
      (complexGram_posSemidef (canonicalFinBlock er ec w.1 w.2 N)).1.eigenvalues₀ i) := by
  let D (w : Matrix (Fin a) (Fin b) ℂ × Matrix (Fin c) (Fin b) ℂ) := canonicalFinBlock er ec w.1 w.2 N
  have hX (u : Fin m) (v : Fin n) : Measurable (fun w => D w u v) := by
    dsimp only [D,canonicalFinBlock,Matrix.coe_reindexLinearEquiv,Matrix.reindex_apply,Matrix.submatrix_apply]
    rcases er.symm u with u|u <;> rcases ec.symm v with v|v <;>
      simp only [Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂] <;> fun_prop
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

private theorem transferAE {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F G : Ω → ℝ) (p C : ℝ) (hp : 0<p) (hC : 0<C)
    (hFm : AEStronglyMeasurable (fun z => (F z)⁻¹^p) μ)
    (hb : ∀ᵐ z ∂μ,0<F z ∧ 0<G z ∧ G z≤C*F z)
    (hI : Integrable (fun z => (G z)⁻¹^p) μ) :
    Integrable (fun z => (F z)⁻¹^p) μ := by
  apply (hI.const_mul (C^p)).mono' hFm
  filter_upwards [hb] with z hz
  change |(F z)⁻¹^p|≤C^p*(G z)⁻¹^p
  rw [abs_of_nonneg (Real.rpow_nonneg (inv_nonneg.mpr hz.1.le) p)]
  have hi : (F z)⁻¹≤C*(G z)⁻¹ := by
    have hh : (1 : ℝ)/F z≤C/G z :=
      (div_le_div_iff₀ hz.1 hz.2.1).mpr (by simpa only [one_mul] using hz.2.2)
    simpa only [one_div,div_eq_mul_inv,one_mul] using hh
  exact (Real.rpow_le_rpow (inv_nonneg.mpr hz.1.le) hi hp.le).trans_eq
    (Real.mul_rpow hC.le (inv_nonneg.mpr hz.2.1.le))

theorem actual_canonical_inverse_realMoment_integrable_iff {m p n b a c : ℕ}
    (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (T : Matrix (Fin n) (Fin b ⊕ Fin c) ℂ) (U : Matrix (Fin p) (Fin b) ℂ)
    (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin a ⊕ Fin c))
    (MA : Matrix (Fin a) (Fin b) ℂ) (MH : Matrix (Fin c) (Fin b) ℂ)
    (N : Matrix (Fin c) (Fin c) ℂ)
    (er : (Fin a ⊕ Fin c) ≃ Fin m) (ec : (Fin b ⊕ Fin c) ≃ Fin n)
    (hBT : B*T=fromCols U 0) (hU : Uᴴ*U=1)
    (hMean : (fromBlocks MA 0 MH N).toEuclideanLin=
      V.toLinearEquiv.toLinearMap.comp (M*T).toEuclideanLin)
    (hT : Function.Bijective T.toEuclideanLin) (hN : IsUnit N.det)
    (hstack : (Matrix.fromRows B M).rank=n)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=min m n)
    (j : Fin (Fintype.card (Fin b))) (hj : j.val+1=min a b)
    (k : Fin (Fintype.card (Fin c))) (hk : k.val+1=c) (q : ℝ) (hq : 0<q) :
    Integrable (fun z => (actualCorrelatedEigenvalue B M i z)⁻¹^q)
      (stdGaussian (ComplexSample (m := m) (n := p))) ↔
      q<((max a b-min a b+1 : ℕ) : ℝ) := by
  let μ := stdGaussian (ComplexSample (m := m) (n := p))
  let Y (z : ComplexSample (m := m) (n := p)) :
      Matrix (Fin a) (Fin b) ℂ × Matrix (Fin c) (Fin b) ℂ :=
    ((fun u v => V (complexMatrixColumn (complexSampleMatrix z*U) v) (Sum.inl u)+MA u v),
     (fun u v => V (complexMatrixColumn (complexSampleMatrix z*U) v) (Sum.inr u)+MH u v))
  let G (w : Matrix (Fin a) (Fin b) ℂ × Matrix (Fin c) (Fin b) ℂ) :=
    (complexGram_posSemidef (canonicalFinBlock er ec w.1 w.2 N)).1.eigenvalues₀ i
  have hYm : Measurable Y := by
    have hZ : Measurable (complexSampleMatrix (m := m) (n := p)) := by
      apply Measurable.of_eval
      intro u
      apply Measurable.of_eval
      intro v
      unfold complexSampleMatrix
      fun_prop
    have hcol (v : Fin b) : Measurable (fun z : ComplexSample (m := m) (n := p) => complexMatrixColumn (complexSampleMatrix z*U) v) := by
      have hout : Measurable (fun A : Matrix (Fin m) (Fin b) ℂ => complexMatrixColumn A v) := by
        unfold complexMatrixColumn
        fun_prop
      exact hout.comp ((continuous_id.matrix_mul continuous_const).measurable.comp hZ)
    apply Measurable.prodMk
    · apply Measurable.of_eval
      intro u
      apply Measurable.of_eval
      intro v
      exact ((by fun_prop : Measurable (fun x : EuclideanSpace ℂ (Fin m) => V x (Sum.inl u))).comp (hcol v)).add_const _
    · apply Measurable.of_eval
      intro u
      apply Measurable.of_eval
      intro v
      exact ((by fun_prop : Measurable (fun x : EuclideanSpace ℂ (Fin m) => V x (Sum.inr u))).comp (hcol v)).add_const _
  have hY : μ.map Y=(complexGaussianMatrixLaw MA).prod (complexGaussianMatrixLaw MH) :=
    actual_sum_isometric_noise_block_law U hU V MA MH
  have hGm : Measurable G := measurableCoordinate er ec N i
  have hPow : Measurable (fun w => (G w)⁻¹^q) := hGm.inv.pow_const q
  have hCanon : Integrable (fun z => (G (Y z))⁻¹^q) μ ↔
      q<((max a b-min a b+1 : ℕ) : ℝ) := by
    have hcrit := canonical_matrix_product_inverse_realMoment_integrable_iff
      ha hb hc er ec MA MH N hN i hi j hj k hk q hq
    rw [← hY,integrable_map_measure hPow.aestronglyMeasurable hYm.aemeasurable] at hcrit
    exact hcrit
  have hm : 0<m := by have hd := Fintype.card_congr er;simp only [Fintype.card_sum,Fintype.card_fin] at hd;omega
  have hn : 0<n := by have hd := Fintype.card_congr ec;simp only [Fintype.card_sum,Fintype.card_fin] at hd;omega
  let F := T.submatrix id ec.symm
  let C := max (matrixColumnControl F) (matrixColumnControl Fᴴ)
  let D := max (matrixColumnControl F⁻¹) (matrixColumnControl (Fᴴ)⁻¹)
  have hC : 0<C := (matrixColumnControl_pos F).trans_le (le_max_left _ _)
  have hD : 0<D := (matrixColumnControl_pos F⁻¹).trans_le (le_max_left _ _)
  have hAE := actual_canonical_fin_positive_bounds_ae B M T U V MA MH N er ec hBT hMean hT hstack hm hn i hi
  have hOrig : AEStronglyMeasurable (fun z => (actualCorrelatedEigenvalue B M i z)⁻¹^q) μ :=
    ((measurable_actualCorrelatedEigenvalue B M i).inv.pow_const q).aestronglyMeasurable
  have hCan : AEStronglyMeasurable (fun z => (G (Y z))⁻¹^q) μ :=
    hPow.aestronglyMeasurable.comp_measurable hYm
  have hequiv : Integrable (fun z => (actualCorrelatedEigenvalue B M i z)⁻¹^q) μ ↔
      Integrable (fun z => (G (Y z))⁻¹^q) μ := by
    constructor
    · intro hI
      apply transferAE μ (fun z => G (Y z)) (actualCorrelatedEigenvalue B M i) q D hq hD hCan _ hI
      filter_upwards [hAE] with z hz
      exact ⟨hz.2.1,hz.1,hz.2.2.2⟩
    · intro hI
      apply transferAE μ (actualCorrelatedEigenvalue B M i) (fun z => G (Y z)) q C hq hC hOrig _ hI
      filter_upwards [hAE] with z hz
      exact ⟨hz.1,hz.2.1,hz.2.2.1⟩
  exact hequiv.trans hCanon

end
end JinWishart
#print axioms JinWishart.actual_canonical_inverse_realMoment_integrable_iff
