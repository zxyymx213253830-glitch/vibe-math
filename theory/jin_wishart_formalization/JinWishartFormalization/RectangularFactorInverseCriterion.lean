import JinWishartFormalization.RectangularFullColumnFrame

/-! Sharp inverse criterion for a fixed full-column-rank rectangular noise
factor on its original 2mp source. Codex. Controls seed2026102238 reused.
[需人工审查] ProperCN1 law, fixed means, AE rank and inverse domination.
No Gaussian invariance is asserted for the nonunitary column factor S. -/
open Matrix Module MeasureTheory ProbabilityTheory
open scoped ComplexOrder
namespace JinWishart
noncomputable section

private theorem matrixCoordinateMeasurable (m n : ℕ) (i : Fin (Fintype.card (Fin n))) :
    Measurable (fun X : Matrix (Fin m) (Fin n) ℂ => (complexGram_posSemidef X).1.eigenvalues₀ i) := by
  change Measurable ((fun Q : HermitianMatrix n => hermitianEigenvalueVector Q i) ∘
    fun X => (⟨complexGram X,(complexGram_posSemidef X).1⟩ : HermitianMatrix n))
  exact ((orderedHermitianEigenvalueCoordinatesContinuous n i).measurable).comp
    ((measurable_complexGram_map m n).subtype_mk (h := fun X => (complexGram_posSemidef X).1))

private theorem iidCriterion {m n : ℕ} (hm : 0<m) (hn : 0<n)
    (M : Matrix (Fin m) (Fin n) ℂ) (i : Fin (Fintype.card (Fin n)))
    (hi : i.val+1=min m n) (q : ℝ) (hq : 0<q) :
    Integrable (fun z => (complexNoncentralSampleEigenvalue M i z)⁻¹^q)
      (stdGaussian (ComplexSample (m := m) (n := n))) ↔
      q<((max m n-min m n+1 : ℕ) : ℝ) := by
  by_cases hnm : n≤m
  · have he : i=smallestEigenvalue₀Index hn := by
      have hj : (smallestEigenvalue₀Index hn).val+1=n := by
        simp [smallestEigenvalue₀Index,Fintype.card_fin];omega
      apply Fin.ext
      rw [Nat.min_eq_right hnm] at hi
      omega
    rw [he,Nat.max_eq_left hnm,Nat.min_eq_right hnm]
    exact actualNoncentralRectangular_inverseMinimum_realMoment_integrable_iff m n hn hnm M q hq
  · have hmn : m≤n := by omega
    rw [Nat.max_eq_right hmn,Nat.min_eq_left hmn]
    exact actualWide_fixed_positive_inverse_realMoment_integrable_iff m n hm hmn M i
      (hi.trans (Nat.min_eq_left hmn)) q hq

private theorem transferAE {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F G : Ω → ℝ) (q C : ℝ) (hq : 0<q) (hC : 0<C)
    (hFm : AEStronglyMeasurable (fun z => (F z)⁻¹^q) μ)
    (hb : ∀ᵐ z ∂μ,0<F z ∧ 0<G z ∧ G z≤C*F z)
    (hI : Integrable (fun z => (G z)⁻¹^q) μ) :
    Integrable (fun z => (F z)⁻¹^q) μ := by
  apply (hI.const_mul (C^q)).mono' hFm
  filter_upwards [hb] with z hz
  change |(F z)⁻¹^q|≤C^q*(G z)⁻¹^q
  rw [abs_of_nonneg (Real.rpow_nonneg (inv_nonneg.mpr hz.1.le) q)]
  have hi : (F z)⁻¹≤C*(G z)⁻¹ := by
    have hh : (1 : ℝ)/F z≤C/G z :=
      (div_le_div_iff₀ hz.1 hz.2.1).mpr (by simpa only [one_mul] using hz.2.2)
    simpa only [one_div,div_eq_mul_inv,one_mul] using hh
  exact (Real.rpow_le_rpow (inv_nonneg.mpr hz.1.le) hi hq.le).trans_eq
    (Real.mul_rpow hC.le (inv_nonneg.mpr hz.2.1.le))

theorem actual_rectangular_factor_inverse_realMoment_integrable_iff {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (hB : B.rank=n) (hm : 0<m) (hn : 0<n)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=min m n) (q : ℝ) (hq : 0<q) :
    Integrable (fun z => (actualCorrelatedEigenvalue B M i z)⁻¹^q)
      (stdGaussian (ComplexSample (m := m) (n := p))) ↔
      q<((max m n-min m n+1 : ℕ) : ℝ) := by
  obtain ⟨S,U,hS,hU,hBS⟩ := exists_rectangular_full_column_frame B hB
  let μ := stdGaussian (ComplexSample (m := m) (n := p))
  let Y (z : ComplexSample (m := m) (n := p)) := complexSampleMatrix z*U+M*S
  let G (X : Matrix (Fin m) (Fin n) ℂ) := (complexGram_posSemidef X).1.eigenvalues₀ i
  have hZ : Measurable (complexSampleMatrix (m := m) (n := p)) := by
    simpa only [add_zero] using measurable_shiftedComplexSampleMatrix (0 : Matrix (Fin m) (Fin p) ℂ)
  have hmul : Measurable (fun X : Matrix (Fin m) (Fin p) ℂ => X*U) :=
    (continuous_id.matrix_mul continuous_const).measurable
  have hYm : Measurable Y := (hmul.comp hZ).add_const _
  have hY : μ.map Y=complexGaussianMatrixLaw (M*S) := by
    have h0 := complexGaussianMatrixLaw_right_isometric_projection (m := m) U hU
    unfold complexGaussianMatrixLaw at h0
    rw [Measure.map_map hmul (measurable_shiftedComplexSampleMatrix _)] at h0
    have h0' : μ.map (fun z => complexSampleMatrix z*U)=
        complexGaussianMatrixLaw (0 : Matrix (Fin m) (Fin n) ℂ) := by
      simpa only [Function.comp_def,add_zero,complexGaussianMatrixLaw] using h0
    have hshift : Measurable (fun X : Matrix (Fin m) (Fin n) ℂ => X+M*S) := by fun_prop
    have hs : (complexGaussianMatrixLaw (0 : Matrix (Fin m) (Fin n) ℂ)).map
        (fun X => X+M*S)=complexGaussianMatrixLaw (M*S) := by
      unfold complexGaussianMatrixLaw
      rw [Measure.map_map hshift (measurable_shiftedComplexSampleMatrix _)]
      congr 1
      funext z
      simp only [Function.comp_def,add_zero]
    have hZu : Measurable (fun z : ComplexSample (m := m) (n := p) =>
        complexSampleMatrix z*U) := hmul.comp hZ
    rw [← h0',Measure.map_map hshift hZu] at hs
    exact hs
  have hPow : Measurable (fun X => (G X)⁻¹^q) := (matrixCoordinateMeasurable m n i).inv.pow_const q
  have hcrit : Integrable (fun X => (G X)⁻¹^q) (complexGaussianMatrixLaw (M*S)) ↔
      q<((max m n-min m n+1 : ℕ) : ℝ) := by
    unfold complexGaussianMatrixLaw
    rw [integrable_map_measure hPow.aestronglyMeasurable
      (measurable_shiftedComplexSampleMatrix _).aemeasurable]
    exact iidCriterion hm hn (M*S) i hi q hq
  rw [← hY,integrable_map_measure hPow.aestronglyMeasurable hYm.aemeasurable] at hcrit
  have hstack : (Matrix.fromRows B M).rank=n := by
    have hl := matrix_fromRows_rank_eq B M
    have hu := (Matrix.fromRows B M).rank_le_card_width
    simp only [Fintype.card_fin] at hu
    omega
  have hrank := actualCorrelatedRank_eq_generic_ae B M
  rw [← matrix_fromRows_rank_eq B M,hstack] at hrank
  let C := max (matrixColumnControl S) (matrixColumnControl Sᴴ)
  let D := max (matrixColumnControl S⁻¹) (matrixColumnControl (Sᴴ)⁻¹)
  have hC : 0<C := (matrixColumnControl_pos S).trans_le (le_max_left _ _)
  have hD : 0<D := (matrixColumnControl_pos S⁻¹).trans_le (le_max_left _ _)
  have hAE : ∀ᵐ z ∂μ,0<actualCorrelatedEigenvalue B M i z ∧ 0<G (Y z) ∧
      G (Y z)≤C*actualCorrelatedEigenvalue B M i z ∧
      actualCorrelatedEigenvalue B M i z≤D*G (Y z) := by
    filter_upwards [hrank] with z hz
    have he : (complexSampleMatrix z*B+M)*S=Y z := by
      rw [Matrix.add_mul,Matrix.mul_assoc,hBS]
    by_cases hnm : n≤m
    · obtain ⟨hx,hy,hu,hl⟩ := full_column_rank_positive_coordinate_mul_bounds
        (complexSampleMatrix z*B+M) S hn hS (hz.trans (Nat.min_eq_right hnm)) i
        (hi.trans (Nat.min_eq_right hnm))
      rw [he] at hy hu hl
      exact ⟨hx,hy,hu.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hx.le),
        hl.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hy.le)⟩
    · have hmn : m≤n := by omega
      obtain ⟨hx,hy,hu,hl⟩ := full_row_rank_positive_coordinate_mul_bounds
        (complexSampleMatrix z*B+M) S hm hS (hz.trans (Nat.min_eq_left hmn)) i
        (hi.trans (Nat.min_eq_left hmn))
      rw [he] at hy hu hl
      exact ⟨hx,hy,hu.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hx.le),
        hl.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hy.le)⟩
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
  exact hequiv.trans hcrit

end
end JinWishart
#print axioms JinWishart.actual_rectangular_factor_inverse_realMoment_integrable_iff
