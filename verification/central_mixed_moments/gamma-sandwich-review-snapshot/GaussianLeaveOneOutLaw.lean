import JinWishartFormalization.GaussianResidualEnergy
import JinWishartFormalization.GramMinimumResidualLower
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Actual marginal laws of measurable leave-one-column-out energies

Codex proofs. Fixed coordinate permutations preserve the same Gaussian source.
Residuals in different columns are NOT asserted to be independent.
[需人工审查] Gaussian coordinate transport and exceptional-rank correspondence.
-/
open Matrix MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

def selectedColumnFirstEquiv {n : ℕ} (j : Fin (n+1)) : Fin (n+1) ≃ Fin (n+1) :=
  (finSuccEquiv' (0 : Fin (n+1))).trans (finSuccEquiv' j).symm

theorem selectedColumnFirstEquiv_zero {n : ℕ} (j : Fin (n+1)) :
    selectedColumnFirstEquiv j 0 = j := by
  simp [selectedColumnFirstEquiv]

theorem selectedColumnFirstEquiv_succ {n : ℕ} (j : Fin (n+1)) (i : Fin n) :
    selectedColumnFirstEquiv j i.succ = j.succAbove i := by
  simp [selectedColumnFirstEquiv,finSuccEquiv']

def totalLeaveOneOutEnergy {m n : ℕ} (j : Fin (n+1))
    (z : ComplexSample (m := m) (n := n+1)) : ℝ :=
  totalColumnResidualEnergy ((complexSampleMatrix z).submatrix id j.succAbove)
    (complexMatrixColumn (complexSampleMatrix z) j)

theorem measurable_totalLeaveOneOutEnergy {m n : ℕ} (j : Fin (n+1)) :
    Measurable (fun z : ComplexSample (m := m) (n := n+1) =>
      totalLeaveOneOutEnergy (m := m) (n := n) j z) := by
  have hA : Measurable (complexSampleMatrix (m := m) (n := n+1)) := by
    simpa only [add_zero] using
      measurable_shiftedComplexSampleMatrix (0 : Matrix (Fin m) (Fin (n+1)) ℂ)
  have hB : Measurable (fun z : ComplexSample (m := m) (n := n+1) =>
      (complexSampleMatrix z).submatrix id j.succAbove) := by
    apply Measurable.of_eval_matrix
    intro i k
    exact hA.eval_matrix
  have hv : Measurable (fun z : ComplexSample (m := m) (n := n+1) =>
      complexMatrixColumn (complexSampleMatrix z) j) := by
    exact (show Continuous (fun A : Matrix (Fin m) (Fin (n+1)) ℂ => complexMatrixColumn A j)
      from by unfold complexMatrixColumn; fun_prop).measurable.comp hA
  unfold totalLeaveOneOutEnergy totalColumnResidualEnergy
  have hG := (measurable_gramInverseProjector_euclidean m n).comp (hB.prodMk hv)
  simpa only [Function.comp_def,Pi.sub_apply] using (hv.sub hG).norm.pow_const 2

theorem actualLeaveOneOut_energy_law {m n : ℕ} (hn : 0 < n) (hnm : n < m)
    (j : Fin (n+1)) :
    (stdGaussian (ComplexSample (m := m) (n := n+1))).map
      (totalLeaveOneOutEnergy (m := m) (n := n) j) =
      gammaMeasure ((m-n : ℕ) : ℝ) 1 := by
  let F := fun z : ComplexSample (m := m) (n := n+1) =>
    totalColumnResidualEnergy (sampleRemainingComplexColumns z) (sampleFirstComplexColumn z)
  have hB : Measurable (sampleRemainingComplexColumns (m := m) (n := n)) := by
    unfold sampleRemainingComplexColumns complexSampleMatrix
    fun_prop
  have hv : Measurable (sampleFirstComplexColumn (m := m) (n := n)) := by
    unfold sampleFirstComplexColumn complexSampleMatrix
    fun_prop
  have hFraw := (measurable_totalColumnResidualEnergy m n).comp (hB.prodMk hv)
  have hF : Measurable F := by simpa only [Function.comp_def,F] using hFraw
  have h := congrArg (fun μ => μ.map F)
    (stdGaussian_sampleColumnSelection_law (m := m) (n := n+1) (k := n+1) (selectedColumnFirstEquiv j)
      (selectedColumnFirstEquiv j).injective)
  rw [Measure.map_map hF (measurable_sampleColumnSelection _)] at h
  have hbase : (stdGaussian (ComplexSample (m := m) (n := n+1))).map F =
      gammaMeasure ((m-n : ℕ) : ℝ) 1 := actualFirstColumn_residual_energy_law hn hnm
  rw [hbase] at h
  have he : F ∘ sampleColumnSelection (selectedColumnFirstEquiv j) = totalLeaveOneOutEnergy j := by
    funext z
    simp only [Function.comp_apply]
    unfold F totalLeaveOneOutEnergy sampleRemainingComplexColumns sampleFirstComplexColumn
    rw [complexSampleMatrix_columnSelection]
    congr 1
  rw [he] at h
  exact h

end
end JinWishart
#print axioms JinWishart.selectedColumnFirstEquiv_zero
#print axioms JinWishart.selectedColumnFirstEquiv_succ
#print axioms JinWishart.measurable_totalLeaveOneOutEnergy
#print axioms JinWishart.actualLeaveOneOut_energy_law
