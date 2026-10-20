import JinWishartFormalization.NonnegativeSpectrumPrelog
import JinWishartFormalization.CorrelatedLogDetLowScale

/-! Expected positive-mode prelog for arbitrary fixed correlated factors.
Codex. This does NOT identify the almost-sure rank by a deterministic formula.
[需人工审查] AE/DCT, ordered-spectrum and model interpretation.
-/
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace JinWishart
noncomputable section

theorem actualCorrelatedMatrixLogDet_prelog_expected_positive_modes {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) :
    Tendsto (fun r : ℝ => (∫ z, actualCorrelatedMatrixLogDet B M r z ∂stdGaussian _)/Real.log r)
      atTop (𝓝 (∫ z : ComplexSample (m := m) (n := p),
        (∑ i, if 0<actualCorrelatedEigenvalue B M i z then (1 : ℝ) else 0) ∂stdGaussian _)) := by
  classical
  have hi (i : Fin (Fintype.card (Fin n))) :
      Integrable (fun z : ComplexSample (m := m) (n := p) =>
        if 0<actualCorrelatedEigenvalue B M i z then (1 : ℝ) else 0) (stdGaussian _) := by
    have hlam := measurable_actualCorrelatedEigenvalue B M i
    have hm : Measurable (fun z : ComplexSample (m := m) (n := p) =>
        if 0<actualCorrelatedEigenvalue B M i z then (1 : ℝ) else 0) :=
      Measurable.ite (measurableSet_lt measurable_const hlam) measurable_const measurable_const
    apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
    exact ae_of_all _ (fun z => by split_ifs <;> norm_num)
  have ht := integral_finiteSpectrumLogDet_prelog_nonneg (stdGaussian _) (actualCorrelatedEigenvalue B M)
    (integrable_actualCorrelatedEigenvalue B M)
    (fun i => ae_of_all _ (actualCorrelatedEigenvalue_nonneg B M i))
  rw [← integral_finsetSum _ (fun i _ => hi i)] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
  have he : (fun z => finiteSpectrumLogDet (fun i => actualCorrelatedEigenvalue B M i z) r) =
      actualCorrelatedMatrixLogDet B M r :=
    funext (fun z => (actualCorrelatedMatrixLogDet_eq_spectral B M r hr z).symm)
  rw [he]

end
end JinWishart
#print axioms JinWishart.actualCorrelatedMatrixLogDet_prelog_expected_positive_modes
