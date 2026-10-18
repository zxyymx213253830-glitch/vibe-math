import JinWishartFormalization.GaussianColumnAppendLaw
import JinWishartFormalization.GaussianComplexMatrixFrame

/-!
# Actual first-row and first-column block laws for complex Gaussian matrices

Codex proofs. Disjoint source coordinates give independence of the full
remaining matrix and the fresh CN(0,1) vector. Transposition transports the
column statement to a row statement without another integration argument.
[需人工审查] Finite coordinate transport and variance convention. No Bartlett
matrix step or Wishart density is assumed here.
-/

open Matrix MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

def standardComplexColumnLaw (m : ℕ) : Measure (EuclideanSpace ℂ (Fin m)) :=
  (stdGaussian (EuclideanSpace ℂ (Fin m))).map (fun v => (Real.sqrt 2)⁻¹ • v)

instance isProbabilityMeasure_standardComplexColumnLaw (m : ℕ) :
    IsProbabilityMeasure (standardComplexColumnLaw m) := by
  unfold standardComplexColumnLaw
  infer_instance

def matrixColumnSplit {m n : ℕ} (A : Matrix (Fin m) (Fin (n + 1)) ℂ) :
    EuclideanSpace ℂ (Fin m) × Matrix (Fin m) (Fin n) ℂ :=
  (complexMatrixColumn A 0, fun i j => A i j.succ)

@[fun_prop]
theorem measurable_matrixColumnSplit (m n : ℕ) :
    Measurable (matrixColumnSplit (m := m) (n := n)) := by
  unfold matrixColumnSplit complexMatrixColumn
  fun_prop

theorem complexGaussianMatrixLaw_columnSplit (m n : ℕ) :
    (complexGaussianMatrixLaw (0 : Matrix (Fin m) (Fin (n + 1)) ℂ)).map matrixColumnSplit =
      (standardComplexColumnLaw m).prod
        (complexGaussianMatrixLaw (0 : Matrix (Fin m) (Fin n) ℂ)) := by
  let F : ComplexSample (m := m) (n := n) × EuclideanSpace ℂ (Fin m) →
      EuclideanSpace ℂ (Fin m) × Matrix (Fin m) (Fin n) ℂ :=
    fun p => ((Real.sqrt 2)⁻¹ • p.2, complexSampleMatrix p.1 + 0)
  have hScale : Measurable
      (fun p : ComplexSample (m := m) (n := n) × EuclideanSpace ℂ (Fin m) =>
        (Real.sqrt (2 : ℝ))⁻¹ • p.2) := by fun_prop
  have hF : Measurable F := by
    simpa only [F, Function.comp_def] using hScale.prodMk
      ((measurable_shiftedComplexSampleMatrix (0 : Matrix (Fin m) (Fin n) ℂ)).comp
        measurable_fst)
  have hS : Measurable (fun v : EuclideanSpace ℂ (Fin m) => (Real.sqrt 2)⁻¹ • v) := by
    fun_prop
  have hProd := (measurable_shiftedComplexSampleMatrix
    (0 : Matrix (Fin m) (Fin n) ℂ)).prodMap hS
  have hProduct : ((stdGaussian (ComplexSample (m := m) (n := n))).prod
      (stdGaussian (EuclideanSpace ℂ (Fin m)))).map F =
      (standardComplexColumnLaw m).prod
        (complexGaussianMatrixLaw (0 : Matrix (Fin m) (Fin n) ℂ)) := by
    change ((stdGaussian (ComplexSample (m := m) (n := n))).prod
      (stdGaussian (EuclideanSpace ℂ (Fin m)))).map
      (Prod.swap ∘ Prod.map (fun z => complexSampleMatrix z + 0)
        (fun v => (Real.sqrt 2)⁻¹ • v)) = _
    rw [← Measure.map_map measurable_swap hProd,
      ← Measure.map_prod_map _ _ (measurable_shiftedComplexSampleMatrix
        (0 : Matrix (Fin m) (Fin n) ℂ)) hS, Measure.prod_swap]
    rfl
  have hpoint (z : ComplexSample (m := m) (n := n + 1)) :
      matrixColumnSplit (complexSampleMatrix z + 0) = F (firstColumnSplit z) := by
    apply Prod.ext
    · change complexMatrixColumn (complexSampleMatrix z + 0) 0 =
        (Real.sqrt 2)⁻¹ • (firstColumnSplit z).2
      rw [add_zero, firstColumnSplit_fresh]
      have hs : (Real.sqrt (2 : ℝ)) ≠ 0 := by positivity
      simp only [smul_smul, inv_mul_cancel₀ hs, one_smul]
      rfl
    · ext i j
      simp only [matrixColumnSplit, F, Matrix.add_apply, Matrix.zero_apply, add_zero]
      exact (firstColumnSplit_previous_apply z i j).symm
  change ((stdGaussian (ComplexSample (m := m) (n := n + 1))).map
    (fun z => complexSampleMatrix z + 0)).map matrixColumnSplit = _
  rw [Measure.map_map (measurable_matrixColumnSplit m n)
    (measurable_shiftedComplexSampleMatrix _)]
  have hfun : matrixColumnSplit ∘ (fun z : ComplexSample (m := m) (n := n + 1) =>
      complexSampleMatrix z + 0) = F ∘ firstColumnSplit := funext hpoint
  rw [hfun, ← Measure.map_map hF (measurable_firstColumnSplit m n), firstColumnSplit_law]
  exact hProduct

def complexSampleTransposeReindex (m n : ℕ) :
    ComplexSample (m := m) (n := n) ≃ₗᵢ[ℝ] ComplexSample (m := n) (n := m) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (Equiv.prodCongr (Equiv.prodComm (Fin m) (Fin n)) (Equiv.refl (Fin 2)))

theorem complexSampleMatrix_transpose_reindex {m n : ℕ}
    (z : ComplexSample (m := m) (n := n)) :
    complexSampleMatrix (complexSampleTransposeReindex m n z) = (complexSampleMatrix z)ᵀ := by
  rfl

theorem complexGaussianMatrixLaw_transpose (m n : ℕ) :
    (complexGaussianMatrixLaw (0 : Matrix (Fin m) (Fin n) ℂ)).map Matrix.transpose =
      complexGaussianMatrixLaw (0 : Matrix (Fin n) (Fin m) ℂ) := by
  change ((stdGaussian (ComplexSample (m := m) (n := n))).map
    (fun z => complexSampleMatrix z + 0)).map Matrix.transpose = _
  rw [Measure.map_map (by fun_prop) (measurable_shiftedComplexSampleMatrix _)]
  have hfun : Matrix.transpose ∘ (fun z : ComplexSample (m := m) (n := n) =>
      complexSampleMatrix z + 0) =
      (fun z => complexSampleMatrix z + (0 : Matrix (Fin n) (Fin m) ℂ)) ∘
        complexSampleTransposeReindex m n := by
    funext z
    simp only [Function.comp_def, add_zero, complexSampleMatrix_transpose_reindex]
  rw [hfun, ← Measure.map_map (measurable_shiftedComplexSampleMatrix _)
    (complexSampleTransposeReindex m n).continuous.measurable, stdGaussian_map]
  rfl

def matrixFirstRow {m n : ℕ} (A : Matrix (Fin (m + 1)) (Fin n) ℂ) :
    EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 (fun j => A 0 j)

def matrixRemainingRows {m n : ℕ} (A : Matrix (Fin (m + 1)) (Fin n) ℂ) :
    Matrix (Fin m) (Fin n) ℂ := fun i j => A i.succ j

def matrixRowSplit {m n : ℕ} (A : Matrix (Fin (m + 1)) (Fin n) ℂ) :
    EuclideanSpace ℂ (Fin n) × Matrix (Fin m) (Fin n) ℂ :=
  (matrixFirstRow A, matrixRemainingRows A)

@[fun_prop]
theorem measurable_matrixRowSplit (m n : ℕ) :
    Measurable (matrixRowSplit (m := m) (n := n)) := by
  unfold matrixRowSplit matrixFirstRow matrixRemainingRows
  fun_prop

/-- Full joint first-row / lower-matrix law in arbitrary dimensions. -/
theorem complexGaussianMatrixLaw_rowSplit (m n : ℕ) :
    (complexGaussianMatrixLaw (0 : Matrix (Fin (m + 1)) (Fin n) ℂ)).map matrixRowSplit =
      (standardComplexColumnLaw n).prod
        (complexGaussianMatrixLaw (0 : Matrix (Fin m) (Fin n) ℂ)) := by
  have hfun : (matrixRowSplit (m := m) (n := n)) =
      Prod.map id Matrix.transpose ∘ matrixColumnSplit ∘ Matrix.transpose := rfl
  rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_map (measurable_matrixColumnSplit n m) (by fun_prop),
    complexGaussianMatrixLaw_transpose, complexGaussianMatrixLaw_columnSplit,
    ← Measure.map_prod_map _ _ measurable_id (by fun_prop),
    Measure.map_id, complexGaussianMatrixLaw_transpose]

end
end JinWishart

#print axioms JinWishart.isProbabilityMeasure_standardComplexColumnLaw
#print axioms JinWishart.measurable_matrixColumnSplit
#print axioms JinWishart.complexGaussianMatrixLaw_columnSplit
#print axioms JinWishart.complexSampleMatrix_transpose_reindex
#print axioms JinWishart.complexGaussianMatrixLaw_transpose
#print axioms JinWishart.measurable_matrixRowSplit
#print axioms JinWishart.complexGaussianMatrixLaw_rowSplit
