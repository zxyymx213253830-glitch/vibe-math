import JinWishartFormalization.GramMinorLogDomination
import JinWishartFormalization.ActualComplexPolynomialLog

/-! Aggregate positive-spectrum logarithm L1 for every FIXED affine factor B,M.
Codex. Physical proper-CN1 source; no nonsingularity or dimension positivity premise.
[需人工审查] Fixed witness choice, AE polynomial/rank null sets, domination and model.
No parameter-uniform estimate or channel-coding interpretation is claimed. -/
open Matrix MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace JinWishart
noncomputable section

theorem coordinate_submatrix_as_compression {m n q : ℕ}
    (X : Matrix (Fin m) (Fin n) ℂ) (f : Fin q → Fin m) (g : Fin q → Fin n) :
    (1 : Matrix (Fin m) (Fin m) ℂ).submatrix f (Equiv.refl _) * X *
      (1 : Matrix (Fin n) (Fin n) ℂ).submatrix (Equiv.refl _) g = X.submatrix f g := by
  rw [Matrix.one_submatrix_mul,Matrix.mul_submatrix_one]
  rfl

theorem exists_actual_fixed_rank_minor_log_witness {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) :
    ∃ (f : Fin (min m (Matrix.fromRows B M).rank) → Fin m)
      (g : Fin (min m (Matrix.fromRows B M).rank) → Fin n),
      Function.Injective f ∧ Function.Injective g ∧
      Integrable (fun z => Real.log ‖((complexSampleMatrix z*B+M).submatrix f g).det‖)
        (stdGaussian (ComplexSample (m := m) (n := p))) ∧
      ∀ᵐ z ∂stdGaussian (ComplexSample (m := m) (n := p)),
        ((complexSampleMatrix z*B+M).submatrix f g).det ≠ 0 := by
  classical
  let r := min m (Matrix.fromRows B M).rank
  obtain ⟨Z₀,hZ₀⟩ := exists_matrix_affine_comp_maximal_rank B M
  rw [← matrix_fromRows_rank_eq] at hZ₀
  have hw := exists_rank_coordinate_minor (Z₀*B+M)
  rw [hZ₀] at hw
  obtain ⟨f,g,hf,hg,hdet⟩ := hw
  let L : Matrix (Fin r) (Fin m) ℂ := (1 : Matrix (Fin m) (Fin m) ℂ).submatrix f (Equiv.refl _)
  let H : Matrix (Fin n) (Fin r) ℂ := (1 : Matrix (Fin n) (Fin n) ℂ).submatrix (Equiv.refl _) g
  have he (X : Matrix (Fin m) (Fin n) ℂ) : L*X*H=X.submatrix f g :=
    coordinate_submatrix_as_compression X f g
  have hlog := integrable_actualAffineCompressedDet_log B M L H
  simp_rw [he] at hlog
  refine ⟨f,g,hf,hg,hlog,?_⟩
  have hp : genericAffineCompressedDet B M L H≠0 := by
    intro hz
    have hv := genericAffineCompressedDet_eval B M L H (complexSampleMean Z₀)
    rw [hz,map_zero,complexSampleMatrix_complexSampleMean,he] at hv
    exact hdet hv.symm
  have ha := sampleEval_ne_zero_ae hp (0 : Matrix (Fin m) (Fin p) ℂ)
  have hm : complexSampleMean (0 : Matrix (Fin m) (Fin p) ℂ)=0 := by
    ext k
    simp [complexSampleMean]
  filter_upwards [ha] with z hz
  have hz' : sampleEval z (genericAffineCompressedDet B M L H)≠0 := by
    simpa only [hm,add_zero] using hz
  simpa only [genericAffineCompressedDet_eval,he] using hz'

theorem integrable_actualCorrelated_positive_log_sum {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) :
    Integrable (fun z => ∑ i, positiveSpectrumLog (actualCorrelatedEigenvalue B M i z))
      (stdGaussian (ComplexSample (m := m) (n := p))) := by
  classical
  let r := min m (Matrix.fromRows B M).rank
  obtain ⟨f,g,hf,hg,hlog,hne⟩ := exists_actual_fixed_rank_minor_log_witness B M
  have ht : Integrable (fun z => ∑ i, actualCorrelatedEigenvalue B M i z) (stdGaussian _) :=
    integrable_finsetSum _ (fun i _ => integrable_actualCorrelatedEigenvalue B M i)
  have hi := (ht.add (integrable_const |Real.log (r.factorial : ℝ)|)).add (hlog.norm.const_mul 2)
  have hm : Measurable (fun z : ComplexSample (m := m) (n := p) =>
      ∑ i, positiveSpectrumLog (actualCorrelatedEigenvalue B M i z)) := by
    apply Finset.measurable_sum
    intro i hi
    unfold positiveSpectrumLog
    exact Measurable.ite (measurableSet_lt measurable_const (measurable_actualCorrelatedEigenvalue B M i))
      (measurable_actualCorrelatedEigenvalue B M i).log measurable_const
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [hne,actualCorrelatedRank_eq_generic_ae B M] with z hz hr
  have hr' : (complexSampleMatrix z*B+M).rank=r := by
    dsimp only [r]
    rw [matrix_fromRows_rank_eq]
    exact hr
  simpa only [Real.norm_eq_abs,Pi.add_apply,Pi.mul_apply,actualCorrelatedEigenvalue] using
    abs_positive_log_sum_le_minor_log (complexSampleMatrix z*B+M) f g hg hr' hz

theorem integrable_actualCorrelated_positive_log {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (i : Fin (Fintype.card (Fin n))) :
    Integrable (fun z => positiveSpectrumLog (actualCorrelatedEigenvalue B M i z))
      (stdGaussian (ComplexSample (m := m) (n := p))) := by
  exact integrable_positiveSpectrumLog_of_sum (stdGaussian _)
    (actualCorrelatedEigenvalue B M) (measurable_actualCorrelatedEigenvalue B M)
    (integrable_actualCorrelatedEigenvalue B M)
    (fun i => ae_of_all _ (actualCorrelatedEigenvalue_nonneg B M i))
    (integrable_actualCorrelated_positive_log_sum B M) i

theorem actualCorrelatedMatrixLogDet_offset_generic_rank {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) :
    Tendsto (fun r : ℝ => (∫ z, actualCorrelatedMatrixLogDet B M r z ∂stdGaussian _)-
      ((min m (Matrix.fromRows B M).rank):ℝ)*Real.log r) atTop
      (𝓝 (∫ z, (∑ i, positiveSpectrumLog (actualCorrelatedEigenvalue B M i z)) ∂stdGaussian _)) := by
  exact actualCorrelatedMatrixLogDet_offset_of_sum_log B M (integrable_actualCorrelated_positive_log_sum B M)

end
end JinWishart
#print axioms JinWishart.coordinate_submatrix_as_compression
#print axioms JinWishart.exists_actual_fixed_rank_minor_log_witness
#print axioms JinWishart.integrable_actualCorrelated_positive_log_sum
#print axioms JinWishart.integrable_actualCorrelated_positive_log
#print axioms JinWishart.actualCorrelatedMatrixLogDet_offset_generic_rank
