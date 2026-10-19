import JinWishartFormalization.GramComplexProjection
import JinWishartFormalization.GaussianColumnAppendLaw

/-!
# Globally measurable actual Gaussian column residual energy

Codex proofs. The total inverse formula agrees with the genuine orthogonal
residual whenever preceding columns have full rank; measurability is global.
[需人工审查] Real/complex projection, exceptional ranks and actual variance.
-/
open Matrix MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

def totalColumnResidualEnergy {m n : ℕ} (B : Matrix (Fin m) (Fin n) ℂ)
    (v : EuclideanSpace ℂ (Fin m)) : ℝ :=
  ‖v-(gramInverseProjector B).toEuclideanLin v‖^2

@[fun_prop]
theorem measurable_totalColumnResidualEnergy (m n : ℕ) :
    Measurable (fun p : Matrix (Fin m) (Fin n) ℂ × EuclideanSpace ℂ (Fin m) =>
      totalColumnResidualEnergy p.1 p.2) := by
  unfold totalColumnResidualEnergy
  exact (measurable_snd.sub (measurable_gramInverseProjector_euclidean m n)).norm.pow_const 2

theorem totalColumnResidualEnergy_eq_complex_residual {m n : ℕ}
    (B : Matrix (Fin m) (Fin n) ℂ) (hB : IsUnit (Bᴴ*B).det)
    (v : EuclideanSpace ℂ (Fin m)) :
    totalColumnResidualEnergy B v = ‖B.toEuclideanLin.rangeᗮ.starProjection v‖^2 := by
  unfold totalColumnResidualEnergy
  rw [← gramInverseProjector_eq_complex_projection B hB]
  have h := B.toEuclideanLin.range.starProjection_add_starProjection_orthogonal v
  rw [(eq_sub_of_add_eq' h).symm]

theorem complexColumnSplitEnergy_eq_total {m n : ℕ}
    (B : Matrix (Fin m) (Fin n) ℂ) (v : EuclideanSpace ℂ (Fin m)) :
    complexColumnSplitEnergy (totalGramColumnSpaceReal B) v =
      (‖(gramInverseProjector B).toEuclideanLin v‖^2,totalColumnResidualEnergy B v) := by
  let K := totalGramColumnSpaceReal B
  have hp := totalGramColumnSpaceReal_projection B v
  have h := K.starProjection_add_starProjection_orthogonal v
  have hr : v-(gramInverseProjector B).toEuclideanLin v = Kᗮ.starProjection v := by
    rw [← hp]
    exact (eq_sub_of_add_eq' h).symm
  change (‖K.starProjection v‖^2,‖Kᗮ.starProjection v‖^2) = _
  rw [hp,totalColumnResidualEnergy,hr]

@[fun_prop]
theorem measurable_complexColumnSplitEnergy_total (m n : ℕ) :
    Measurable (fun p : Matrix (Fin m) (Fin n) ℂ × EuclideanSpace ℂ (Fin m) =>
      complexColumnSplitEnergy (totalGramColumnSpaceReal p.1) p.2) := by
  simp_rw [complexColumnSplitEnergy_eq_total]
  exact (measurable_gramInverseProjector_euclidean m n).norm.pow_const 2 |>.prodMk
    (measurable_totalColumnResidualEnergy m n)

theorem actualFirstColumn_residual_energy_law {m n : ℕ} (hn : 0 < n) (hnm : n < m) :
    (stdGaussian (ComplexSample (m := m) (n := n+1))).map
      (fun z => totalColumnResidualEnergy (sampleRemainingComplexColumns z) (sampleFirstComplexColumn z)) =
        gammaMeasure ((m-n : ℕ) : ℝ) 1 := by
  let μ := complexGaussianMatrixLaw (0 : Matrix (Fin m) (Fin n) ℂ)
  let γ₁ := gammaMeasure (n : ℝ) 1
  let γ₂ := gammaMeasure ((m-n : ℕ) : ℝ) 1
  letI : IsProbabilityMeasure γ₁ := isProbabilityMeasure_gammaMeasure (by exact_mod_cast hn) (by norm_num)
  letI : IsProbabilityMeasure γ₂ := isProbabilityMeasure_gammaMeasure
    (by exact_mod_cast (Nat.sub_pos_of_lt hnm)) (by norm_num)
  have h := congrArg (fun ν => ν.map (fun p : Matrix (Fin m) (Fin n) ℂ × (ℝ × ℝ) => p.2.2))
    (actualColumnAppend_split_energy_law hn hnm)
  have hB : Measurable (sampleRemainingComplexColumns (m := m) (n := n)) := by
    unfold sampleRemainingComplexColumns complexSampleMatrix
    fun_prop
  have hv : Measurable (sampleFirstComplexColumn (m := m) (n := n)) := by
    unfold sampleFirstComplexColumn complexSampleMatrix
    fun_prop
  have hE := (measurable_complexColumnSplitEnergy_total m n).comp (hB.prodMk hv)
  have hF : Measurable (fun z : ComplexSample (m := m) (n := n+1) =>
      (sampleRemainingComplexColumns z,
        complexColumnSplitEnergy (totalGramColumnSpaceReal (sampleRemainingComplexColumns z))
          (sampleFirstComplexColumn z))) := by
    simpa only [Function.comp_apply] using hB.prodMk hE
  have hproj : MeasurePreserving (fun p : Matrix (Fin m) (Fin n) ℂ × (ℝ × ℝ) => p.2.2)
      (μ.prod (γ₁.prod γ₂)) γ₂ :=
    (measurePreserving_snd (μ := γ₁) (ν := γ₂)).comp
      (measurePreserving_snd (μ := μ) (ν := γ₁.prod γ₂))
  rw [Measure.map_map (by fun_prop) hF,hproj.map_eq] at h
  simpa only [Function.comp_def,complexColumnSplitEnergy_eq_total] using h

end
end JinWishart
#print axioms JinWishart.measurable_totalColumnResidualEnergy
#print axioms JinWishart.totalColumnResidualEnergy_eq_complex_residual
#print axioms JinWishart.complexColumnSplitEnergy_eq_total
#print axioms JinWishart.measurable_complexColumnSplitEnergy_total
#print axioms JinWishart.actualFirstColumn_residual_energy_law
