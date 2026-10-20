import JinWishartFormalization.NonnegativeSpectrumOffset
import JinWishartFormalization.CorrelatedLogDetGenericRank

/-! General fixed-factor offset CONDITIONAL on absolute positive-log moments.
Codex. The log-moment premise is OPEN for arbitrary B/M; this is not an unconditional law.
[需人工审查] Positive-mode restriction, Gaussian rank null sets, integration and model.
-/
open Matrix Module MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace JinWishart
noncomputable section

theorem actualCorrelatedMatrixLogDet_offset_of_log_moments {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (hlog : ∀ i, Integrable (fun z => positiveSpectrumLog (actualCorrelatedEigenvalue B M i z))
      (stdGaussian _)) :
    Tendsto (fun r : ℝ => (∫ z, actualCorrelatedMatrixLogDet B M r z ∂stdGaussian _)-
      ((min m (Matrix.fromRows B M).rank):ℝ)*Real.log r) atTop
      (𝓝 (∫ z, (∑ i, positiveSpectrumLog (actualCorrelatedEigenvalue B M i z)) ∂stdGaussian _)) := by
  classical
  have hi (i : Fin (Fintype.card (Fin n))) :
      Integrable (fun z : ComplexSample (m := m) (n := p) =>
        if 0<actualCorrelatedEigenvalue B M i z then (1:ℝ) else 0) (stdGaussian _) := by
    have hm : Measurable (fun z : ComplexSample (m := m) (n := p) =>
        if 0<actualCorrelatedEigenvalue B M i z then (1:ℝ) else 0) := Measurable.ite
      (measurableSet_lt measurable_const (measurable_actualCorrelatedEigenvalue B M i))
      measurable_const measurable_const
    apply (integrable_const (1:ℝ)).mono' hm.aestronglyMeasurable
    exact ae_of_all _ (fun z => by split_ifs <;> norm_num)
  have hmass (i : Fin (Fintype.card (Fin n))) :
      (stdGaussian _).real {z | 0<actualCorrelatedEigenvalue B M i z} =
      ∫ z : ComplexSample (m := m) (n := p),
        (if 0<actualCorrelatedEigenvalue B M i z then (1:ℝ) else 0) ∂stdGaussian _ := by
    symm
    simpa [Set.indicator_apply] using
      integral_indicator_const (μ := stdGaussian (ComplexSample (m := m) (n := p))) (1:ℝ)
        (measurableSet_lt measurable_const (measurable_actualCorrelatedEigenvalue B M i))
  have hq : (∑ i, (stdGaussian _).real {z | 0<actualCorrelatedEigenvalue B M i z})=
      ((min m (Matrix.fromRows B M).rank):ℝ) := by
    simp_rw [hmass]
    rw [← integral_finsetSum _ (fun i _ => hi i)]
    calc
      _ = ∫ z : ComplexSample (m := m) (n := p), ((complexSampleMatrix z*B+M).rank:ℝ) ∂stdGaussian _ :=
        integral_congr_ae (ae_of_all _ (fun z => gram_positive_modes_eq_rank _))
      _ = ∫ _z : ComplexSample (m := m) (n := p), ((min m (Matrix.fromRows B M).rank):ℝ) ∂stdGaussian _ := by
        apply integral_congr_ae
        filter_upwards [actualCorrelatedRank_eq_generic_ae B M] with z hz
        rw [matrix_fromRows_rank_eq]
        exact_mod_cast hz
      _ = _ := by simp
  have ht := integral_finiteSpectrumLogDet_offset_nonneg (stdGaussian _)
    (actualCorrelatedEigenvalue B M) (measurable_actualCorrelatedEigenvalue B M)
    (integrable_actualCorrelatedEigenvalue B M)
    (fun i => ae_of_all _ (actualCorrelatedEigenvalue_nonneg B M i)) hlog
  rw [hq,← integral_finsetSum _ (fun i _ => hlog i)] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with r hr
  have he : (fun z => finiteSpectrumLogDet (fun i => actualCorrelatedEigenvalue B M i z) r)=
      actualCorrelatedMatrixLogDet B M r :=
    funext (fun z => (actualCorrelatedMatrixLogDet_eq_spectral B M r hr z).symm)
  rw [he]

end
end JinWishart
#print axioms JinWishart.actualCorrelatedMatrixLogDet_offset_of_log_moments
