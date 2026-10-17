import JinWishartFormalization.GaussianGramEnergyLaw
import JinWishartFormalization.GaussianComplexColumnFrame

/-!
# One new column in an actual Gaussian matrix, arbitrary dimensions

Codex proofs. A finite real coordinate permutation separates the first column
from all remaining n columns. A real isometry then identifies the fresh column
with a standard real Gaussian on the complex column space. Its actual CN(0,1)
entries have an additional division by sqrt2, which is accounted for explicitly
in the projected energies. No measurable QR basis or target density is assumed.
[需人工审查] Product-law transport, indexing, variance and the use of the
existing random-subspace energy law. This is not a full Bartlett matrix law.
-/

open Matrix MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

def firstColumnIndexEquiv (m n : ℕ) :
    ((Fin m × Fin 2) ⊕ ((Fin m × Fin n) × Fin 2)) ≃
      ((Fin m × Fin (n + 1)) × Fin 2) where
  toFun := Sum.elim (fun ik => ((ik.1, 0), ik.2))
    (fun ijk => ((ijk.1.1, ijk.1.2.succ), ijk.2))
  invFun := fun ijk => Fin.cases (.inl (ijk.1.1, ijk.2))
    (fun j => .inr ((ijk.1.1, j), ijk.2)) ijk.1.2
  left_inv := by
    intro x
    cases x <;> rfl
  right_inv := by
    rintro ⟨⟨i, j⟩, k⟩
    induction j using Fin.cases <;> rfl

def firstColumnReindex (m n : ℕ) : ComplexSample (m := m) (n := n + 1) ≃ₗᵢ[ℝ]
    EuclideanSpace ℝ ((Fin m × Fin 2) ⊕ ((Fin m × Fin n) × Fin 2)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (firstColumnIndexEquiv m n).symm

def firstColumnSplitReal {m n : ℕ} (z : ComplexSample (m := m) (n := n + 1)) :
    TwoColumnBlock m × ComplexSample (m := m) (n := n) :=
  euclideanGaussianSplit (firstColumnReindex m n z)

theorem measurable_firstColumnSplitReal (m n : ℕ) :
    Measurable (firstColumnSplitReal (m := m) (n := n)) :=
  measurable_euclideanGaussianSplit.comp (firstColumnReindex m n).continuous.measurable

theorem firstColumnSplitReal_law (m n : ℕ) :
    (stdGaussian (ComplexSample (m := m) (n := n + 1))).map firstColumnSplitReal =
      (stdGaussian (TwoColumnBlock m)).prod
        (stdGaussian (ComplexSample (m := m) (n := n))) := by
  change (stdGaussian (ComplexSample (m := m) (n := n + 1))).map
    (euclideanGaussianSplit ∘ firstColumnReindex m n) = _
  rw [← Measure.map_map measurable_euclideanGaussianSplit (by fun_prop),
    stdGaussian_map, stdGaussian_sum_split]

/-- Return preceding raw sample coordinates, then the fresh unscaled real Gaussian. -/
def firstColumnSplit {m n : ℕ} (z : ComplexSample (m := m) (n := n + 1)) :
    ComplexSample (m := m) (n := n) × EuclideanSpace ℂ (Fin m) :=
  ((firstColumnSplitReal z).2, complexColumnCoordinates m (firstColumnSplitReal z).1)

theorem measurable_firstColumnSplit (m n : ℕ) :
    Measurable (firstColumnSplit (m := m) (n := n)) :=
  ((measurable_firstColumnSplitReal m n).snd).prodMk
    ((complexColumnCoordinates m).continuous.measurable.comp
      (measurable_firstColumnSplitReal m n).fst)

theorem firstColumnSplit_law (m n : ℕ) :
    (stdGaussian (ComplexSample (m := m) (n := n + 1))).map firstColumnSplit =
      (stdGaussian (ComplexSample (m := m) (n := n))).prod
        (stdGaussian (EuclideanSpace ℂ (Fin m))) := by
  change (stdGaussian (ComplexSample (m := m) (n := n + 1))).map
    ((fun p : TwoColumnBlock m × ComplexSample (m := m) (n := n) =>
      (p.2, complexColumnCoordinates m p.1)) ∘ firstColumnSplitReal) = _
  rw [← Measure.map_map (by fun_prop) (measurable_firstColumnSplitReal m n),
    firstColumnSplitReal_law]
  have hfun : (fun p : TwoColumnBlock m × ComplexSample (m := m) (n := n) =>
      (p.2, complexColumnCoordinates m p.1)) =
      Prod.swap ∘ Prod.map (complexColumnCoordinates m) id := rfl
  rw [hfun, ← Measure.map_map measurable_swap (by fun_prop),
    ← Measure.map_prod_map _ _ (complexColumnCoordinates m).continuous.measurable measurable_id,
    stdGaussian_map, Measure.map_id, Measure.prod_swap]

theorem firstColumnSplit_previous_apply {m n : ℕ}
    (z : ComplexSample (m := m) (n := n + 1)) (i : Fin m) (j : Fin n) :
    complexSampleMatrix (firstColumnSplit z).1 i j = complexSampleMatrix z i j.succ := by
  rfl

theorem firstColumnSplit_fresh_apply {m n : ℕ}
    (z : ComplexSample (m := m) (n := n + 1)) (i : Fin m) :
    (firstColumnSplit z).2 i = (z ((i, 0), 0) : ℂ) + z ((i, 0), 1) * Complex.I := by
  rfl

def sampleFirstComplexColumn {m n : ℕ} (z : ComplexSample (m := m) (n := n + 1)) :
    EuclideanSpace ℂ (Fin m) := WithLp.toLp 2 (fun i => complexSampleMatrix z i 0)

def sampleRemainingComplexColumns {m n : ℕ} (z : ComplexSample (m := m) (n := n + 1)) :
    Matrix (Fin m) (Fin n) ℂ := fun i j => complexSampleMatrix z i j.succ

theorem firstColumnSplit_previous {m n : ℕ}
    (z : ComplexSample (m := m) (n := n + 1)) :
    complexSampleMatrix (firstColumnSplit z).1 = sampleRemainingComplexColumns z := by
  ext i j
  exact firstColumnSplit_previous_apply z i j

theorem firstColumnSplit_fresh {m n : ℕ}
    (z : ComplexSample (m := m) (n := n + 1)) :
    (firstColumnSplit z).2 = Real.sqrt 2 • sampleFirstComplexColumn z := by
  have hs : (Real.sqrt (2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)
  ext i
  rw [firstColumnSplit_fresh_apply]
  simp only [sampleFirstComplexColumn, PiLp.smul_apply,
    Complex.real_smul, complexSampleMatrix]
  field_simp

/-- Squared projection norms of an actual CN(0,1) vector (no factor 1/2). -/
def complexColumnSplitEnergy {m : ℕ}
    (K : Submodule ℝ (EuclideanSpace ℂ (Fin m))) (v : EuclideanSpace ℂ (Fin m)) : ℝ × ℝ :=
  (‖K.orthogonalProjectionOnto v‖ ^ 2, ‖Kᗮ.orthogonalProjectionOnto v‖ ^ 2)

theorem gaussianSplitEnergy_sqrtTwo {m : ℕ}
    (K : Submodule ℝ (EuclideanSpace ℂ (Fin m))) (v : EuclideanSpace ℂ (Fin m)) :
    gaussianSplitEnergy K (Real.sqrt 2 • v) = complexColumnSplitEnergy K v := by
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  simp only [gaussianSplitEnergy, complexColumnSplitEnergy, map_smul, norm_smul,
    Real.norm_eq_abs, abs_of_pos hs, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1 <;> ring

/-- One arbitrary-dimensional actual sample supplies both the preceding matrix
and a fresh independent central column. Ranks are proved, not hypotheses. -/
theorem actualColumnAppend_split_energy_law {m n : ℕ} (hn : 0 < n) (hnm : n < m) :
    (stdGaussian (ComplexSample (m := m) (n := n + 1))).map
      (fun z => (sampleRemainingComplexColumns z,
        complexColumnSplitEnergy (totalGramColumnSpaceReal (sampleRemainingComplexColumns z))
          (sampleFirstComplexColumn z))) =
      (complexGaussianMatrixLaw (0 : Matrix (Fin m) (Fin n) ℂ)).prod
        ((gammaMeasure (n : ℝ) 1).prod (gammaMeasure ((m - n : ℕ) : ℝ) 1)) := by
  have hLaw := complexSample_freshGaussian_split_energy hn hnm
    (0 : Matrix (Fin m) (Fin n) ℂ)
  have hInput : Measurable
      (fun p : ComplexSample (m := m) (n := n) × EuclideanSpace ℂ (Fin m) =>
        (complexSampleMatrix p.1 + (0 : Matrix (Fin m) (Fin n) ℂ), p.2)) :=
    ((measurable_shiftedComplexSampleMatrix (0 : Matrix (Fin m) (Fin n) ℂ)).comp
      measurable_fst).prodMk measurable_snd
  have hEnergy := (measurable_gaussianSplitEnergy totalGramColumnSpaceReal
    (measurable_totalGramColumnSpaceReal_projection m n)).comp hInput
  have hF := ((measurable_shiftedComplexSampleMatrix
    (0 : Matrix (Fin m) (Fin n) ℂ)).comp measurable_fst).prodMk hEnergy
  simp only [Function.comp_def] at hF
  rw [← firstColumnSplit_law m n, Measure.map_map hF
    (measurable_firstColumnSplit m n)] at hLaw
  convert hLaw using 1
  congr 1
  funext z
  simp only [Function.comp_def, add_zero, firstColumnSplit_previous, firstColumnSplit_fresh,
    gaussianSplitEnergy_sqrtTwo]

end
end JinWishart

#print axioms JinWishart.measurable_firstColumnSplitReal
#print axioms JinWishart.firstColumnSplitReal_law
#print axioms JinWishart.measurable_firstColumnSplit
#print axioms JinWishart.firstColumnSplit_law
#print axioms JinWishart.firstColumnSplit_previous_apply
#print axioms JinWishart.firstColumnSplit_fresh_apply
#print axioms JinWishart.firstColumnSplit_previous
#print axioms JinWishart.firstColumnSplit_fresh
#print axioms JinWishart.gaussianSplitEnergy_sqrtTwo
#print axioms JinWishart.actualColumnAppend_split_energy_law
