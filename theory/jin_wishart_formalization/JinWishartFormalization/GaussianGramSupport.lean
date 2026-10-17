import JinWishartFormalization.GaussianGramFullRank

/-!
# Strict positive support in both rectangular Gaussian Gram orientations

Codex proofs. Reuse the generic row Gram/witness and the already-proved
polynomial null-set transfer, then choose the paper's smaller-side matrix.
No general Wishart density is assumed or established.
[需人工审查] Inherited Gaussian null-set argument, matrix-event measurability
and the correspondence of the smaller-side orientation with paper notation.
-/

open Matrix MeasureTheory ProbabilityTheory
open scoped ComplexOrder
namespace JinWishart
noncomputable section
variable {m n : ℕ}

theorem genericComplexRowGram_det_eval (z : ComplexSample (m := m) (n := n)) :
    sampleEval z (genericComplexRowGram m n).det =
      (complexSampleMatrix z * (complexSampleMatrix z)ᴴ).det := by
  rw [RingHom.map_det]
  change ((genericComplexRowGram m n).map (sampleEval z)).det = _
  rw [genericComplexRowGram_map]

theorem rowGram_witnessRowMean_det_ne_zero (hmn : m ≤ n) :
    (witnessRowMean hmn * (witnessRowMean hmn)ᴴ).det ≠ 0 := by
  rw [rowGram_witnessRowMean, Matrix.det_diagonal]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact_mod_cast (show (((i : ℕ) : ℝ) + 1) ^ 2 ≠ 0 by positivity)

theorem genericComplexRowGram_det_ne_zero (hmn : m ≤ n) :
    (genericComplexRowGram m n).det ≠ 0 := by
  intro hzero
  have h := genericComplexRowGram_det_eval (complexSampleMean (witnessRowMean hmn))
  rw [hzero, map_zero, complexSampleMatrix_complexSampleMean] at h
  exact rowGram_witnessRowMean_det_ne_zero hmn h.symm

theorem complexSample_shiftedRowGram_det_ne_zero_ae (hmn : m ≤ n)
    (M : Matrix (Fin m) (Fin n) ℂ) :
    ∀ᵐ z ∂stdGaussian (ComplexSample (m := m) (n := n)),
      ((complexSampleMatrix z + M) * (complexSampleMatrix z + M)ᴴ).det ≠ 0 := by
  have h := sampleEval_ne_zero_ae (genericComplexRowGram_det_ne_zero hmn) M
  filter_upwards [h] with z hz
  rwa [genericComplexRowGram_det_eval, complexSampleMatrix_add_mean] at hz

theorem complexSample_shiftedRowGram_posDef_ae (hmn : m ≤ n)
    (M : Matrix (Fin m) (Fin n) ℂ) :
    ∀ᵐ z ∂stdGaussian (ComplexSample (m := m) (n := n)),
      ((complexSampleMatrix z + M) * (complexSampleMatrix z + M)ᴴ).PosDef := by
  filter_upwards [complexSample_shiftedRowGram_det_ne_zero_ae hmn M] with z hz
  exact (Matrix.posSemidef_self_mul_conjTranspose _).posDef_iff_det_ne_zero.mpr hz

/-- Any rectangular shape and fixed mean: the actual smaller-side Gram is PD a.s. -/
theorem paperSmallSideGram_posDef_ae (M : Matrix (Fin m) (Fin n) ℂ) :
    ∀ᵐ z ∂stdGaussian (ComplexSample (m := m) (n := n)),
      (paperSmallSideGram (complexSampleMatrix z + M)).PosDef := by
  classical
  by_cases hmn : m ≤ n
  · filter_upwards [complexSample_shiftedRowGram_posDef_ae hmn M] with z hz
    simpa [paperSmallSideGram, hmn] using
      hz.submatrix (finMinEquivLeft hmn).injective
  · have hnm : n ≤ m := le_of_not_ge hmn
    filter_upwards [complexSample_shiftedGram_posDef_ae hnm M] with z hz
    simpa [paperSmallSideGram, hmn, complexGram] using
      hz.submatrix (finMinEquivRight hnm).injective

theorem measurableSet_complex_posDef (n : ℕ) :
    MeasurableSet {A : Matrix (Fin n) (Fin n) ℂ | A.PosDef} := by
  have hset : {A : Matrix (Fin n) (Fin n) ℂ | A.PosDef} =
      {A | A.PosSemidef} ∩ {A | A.det ≠ 0} := by
    ext A
    exact ⟨fun h => ⟨h.posSemidef, h.posSemidef.posDef_iff_det_ne_zero.mp h⟩,
      fun h => h.1.posDef_iff_det_ne_zero.mpr h.2⟩
  rw [hset]
  exact Matrix.posSemidef_is_closed.measurableSet.inter
    (isOpen_ne.preimage continuous_id.matrix_det).measurableSet

theorem complexNoncentralWishart_posDef_ae (hnm : n ≤ m)
    (M : Matrix (Fin m) (Fin n) ℂ) :
    ∀ᵐ W ∂complexNoncentralWishart M, W.PosDef := by
  apply (ae_map_iff (measurable_shiftedComplexSampleGram M).aemeasurable
    (measurableSet_complex_posDef n)).2
  exact complexSample_shiftedGram_posDef_ae hnm M

theorem complexNoncentralWishart_measure_posDef (hnm : n ≤ m)
    (M : Matrix (Fin m) (Fin n) ℂ) :
    complexNoncentralWishart M {W | W.PosDef} = 1 := by
  exact (mem_ae_iff_prob_eq_one (measurableSet_complex_posDef n)).mp
    (complexNoncentralWishart_posDef_ae hnm M)

end
end JinWishart

#print axioms JinWishart.genericComplexRowGram_det_eval
#print axioms JinWishart.rowGram_witnessRowMean_det_ne_zero
#print axioms JinWishart.genericComplexRowGram_det_ne_zero
#print axioms JinWishart.complexSample_shiftedRowGram_det_ne_zero_ae
#print axioms JinWishart.complexSample_shiftedRowGram_posDef_ae
#print axioms JinWishart.paperSmallSideGram_posDef_ae
#print axioms JinWishart.measurableSet_complex_posDef
#print axioms JinWishart.complexNoncentralWishart_posDef_ae
#print axioms JinWishart.complexNoncentralWishart_measure_posDef
