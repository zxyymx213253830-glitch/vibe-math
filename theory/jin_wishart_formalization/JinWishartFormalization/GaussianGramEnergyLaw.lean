import JinWishartFormalization.GaussianGramFullRank

/-!
# Actual Gaussian preceding columns in the random-subspace energy law

Codex proofs. The preceding matrix has its actual shifted CN(0,1) law, and
the fresh vector is independent standard real Gaussian on the complex column
space. The half squared norms therefore use the CN(0,1) energy convention.
No a.e. full-rank or rank hypotheses remain in these public laws: they are
discharged by GaussianGramFullRank. This is not a full Bartlett matrix law.
[需人工审查] Joint measurability, skew products and real/complex variance.
-/

open Matrix MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section
variable {m n : ℕ}

theorem measurable_shiftedComplexSampleMatrix (M : Matrix (Fin m) (Fin n) ℂ) :
    Measurable (fun z : ComplexSample (m := m) (n := n) => complexSampleMatrix z + M) := by
  apply Measurable.of_eval_matrix
  intro i j
  simp only [Matrix.add_apply, complexSampleMatrix]
  fun_prop

def complexGaussianMatrixLaw (M : Matrix (Fin m) (Fin n) ℂ) :
    Measure (Matrix (Fin m) (Fin n) ℂ) :=
  (stdGaussian (ComplexSample (m := m) (n := n))).map
    (fun z => complexSampleMatrix z + M)

instance isProbabilityMeasure_complexGaussianMatrixLaw (M : Matrix (Fin m) (Fin n) ℂ) :
    IsProbabilityMeasure (complexGaussianMatrixLaw M) := by
  unfold complexGaussianMatrixLaw
  infer_instance

theorem measurableSet_gram_det_isUnit (m n : ℕ) :
    MeasurableSet {A : Matrix (Fin m) (Fin n) ℂ | IsUnit (Aᴴ * A).det} := by
  simp only [isUnit_iff_ne_zero]
  exact (isOpen_ne.preimage (by fun_prop : Continuous
    (fun A : Matrix (Fin m) (Fin n) ℂ => (Aᴴ * A).det))).measurableSet

theorem complexGaussianMatrixLaw_gram_isUnit_ae (hnm : n ≤ m)
    (M : Matrix (Fin m) (Fin n) ℂ) :
    ∀ᵐ A ∂complexGaussianMatrixLaw M, IsUnit (Aᴴ * A).det := by
  apply (ae_map_iff (measurable_shiftedComplexSampleMatrix M).aemeasurable
    (measurableSet_gram_det_isUnit m n)).2
  exact complexSample_shiftedGram_isUnit_det_ae hnm M

/-- Actual preceding-matrix law, with no abstract rank/full-rank assumptions. -/
theorem complexGaussianMatrixLaw_split_energy (hn : 0 < n) (hnm : n < m)
    (M : Matrix (Fin m) (Fin n) ℂ) :
    ((complexGaussianMatrixLaw M).prod (stdGaussian (EuclideanSpace ℂ (Fin m)))).map
      (fun p => (p.1, gaussianSplitEnergy (totalGramColumnSpaceReal p.1) p.2)) =
      (complexGaussianMatrixLaw M).prod
        ((gammaMeasure (n : ℝ) 1).prod (gammaMeasure ((m - n : ℕ) : ℝ) 1)) := by
  exact stdGaussian_gram_column_energy_law m n (complexGaussianMatrixLaw M) hn hnm
    (complexGaussianMatrixLaw_gram_isUnit_ae (Nat.le_of_lt hnm) M)

/-- The preceding actual real Gaussian source can also be kept explicit. -/
theorem complexSample_freshGaussian_split_energy (hn : 0 < n) (hnm : n < m)
    (M : Matrix (Fin m) (Fin n) ℂ) :
    ((stdGaussian (ComplexSample (m := m) (n := n))).prod
      (stdGaussian (EuclideanSpace ℂ (Fin m)))).map
      (fun p => (complexSampleMatrix p.1 + M,
        gaussianSplitEnergy (totalGramColumnSpaceReal (complexSampleMatrix p.1 + M)) p.2)) =
      (complexGaussianMatrixLaw M).prod
        ((gammaMeasure (n : ℝ) 1).prod (gammaMeasure ((m - n : ℕ) : ℝ) 1)) := by
  have hmap : ((stdGaussian (ComplexSample (m := m) (n := n))).prod
      (stdGaussian (EuclideanSpace ℂ (Fin m)))).map
      (Prod.map (fun z => complexSampleMatrix z + M) id) =
      (complexGaussianMatrixLaw M).prod (stdGaussian (EuclideanSpace ℂ (Fin m))) := by
    rw [← Measure.map_prod_map _ _ (measurable_shiftedComplexSampleMatrix M) measurable_id,
      Measure.map_id]
    rfl
  have hLaw := complexGaussianMatrixLaw_split_energy hn hnm M
  rw [← hmap, Measure.map_map
    (measurable_fst.prodMk (measurable_gaussianSplitEnergy totalGramColumnSpaceReal
      (measurable_totalGramColumnSpaceReal_projection m n)))
    ((measurable_shiftedComplexSampleMatrix M).prodMap measurable_id)] at hLaw
  exact hLaw

end
end JinWishart

#print axioms JinWishart.measurable_shiftedComplexSampleMatrix
#print axioms JinWishart.isProbabilityMeasure_complexGaussianMatrixLaw
#print axioms JinWishart.measurableSet_gram_det_isUnit
#print axioms JinWishart.complexGaussianMatrixLaw_gram_isUnit_ae
#print axioms JinWishart.complexGaussianMatrixLaw_split_energy
#print axioms JinWishart.complexSample_freshGaussian_split_energy
