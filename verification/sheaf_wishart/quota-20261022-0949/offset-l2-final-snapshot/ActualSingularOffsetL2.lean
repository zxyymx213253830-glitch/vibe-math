import JinWishartFormalization.FiniteSpectrumOffsetL2
import JinWishartFormalization.ActualSingularPositiveLogSquare

/-! Actual fixed arbitrary-factor random full-logdet offset converges in mean square.
One shared Gaussian sample for every scale; deterministic generic rank is subtracted.
Codex. [需人工审查] AE rank substitution, DCT and physical model correspondence. -/
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace JinWishart
noncomputable section

theorem actualCorrelatedMatrixLogDet_offset_mean_square {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) :
    let R : ℝ := (min m (Matrix.fromRows B M).rank : ℕ)
    let S := fun z : ComplexSample (m := m) (n := p)=>∑ i,positiveSpectrumLog (actualCorrelatedEigenvalue B M i z)
    (∀ r : ℝ,1≤r → Integrable (fun z=>(actualCorrelatedMatrixLogDet B M r z-R*Real.log r-S z)^2) (stdGaussian _)) ∧
    Tendsto (fun r : ℝ=>∫ z,(actualCorrelatedMatrixLogDet B M r z-R*Real.log r-S z)^2 ∂stdGaussian _) atTop (𝓝 0) := by
  classical
  intro R S
  have ht := integral_finiteSpectrumOffsetError_sq_tendsto (stdGaussian _) (actualCorrelatedEigenvalue B M)
    (measurable_actualCorrelatedEigenvalue B M)
    (fun i=>ae_of_all _ (actualCorrelatedEigenvalue_nonneg B M i))
    (integrable_actualCorrelatedEigenvalue_sq B M) (integrable_actualCorrelated_positive_log_sq B M)
  have he (r : ℝ) (hr : 1≤r) : ∀ᵐ z ∂stdGaussian (ComplexSample (m := m) (n := p)),
      (∑ i,positiveModeOffsetError (actualCorrelatedEigenvalue B M i z) r)=
        actualCorrelatedMatrixLogDet B M r z-R*Real.log r-S z := by
    filter_upwards [actualCorrelatedRank_eq_generic_ae B M] with z hz
    have hc := gram_positive_modes_eq_rank (complexSampleMatrix z*B+M)
    change (∑ i,if 0<actualCorrelatedEigenvalue B M i z then (1:ℝ) else 0)=_ at hc
    have hR : ((complexSampleMatrix z*B+M).rank : ℝ)=R := by
      rw [hz,← matrix_fromRows_rank_eq]
    have hcount := hc.trans hR
    have hC : (∑ i,Real.log (1+r*actualCorrelatedEigenvalue B M i z))=actualCorrelatedMatrixLogDet B M r z := by
      simpa only [finiteSpectrumLogDet] using
        (actualCorrelatedMatrixLogDet_eq_spectral B M r (zero_le_one.trans hr) z).symm
    unfold positiveModeOffsetError
    rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,← Finset.sum_mul,hcount,hC]
  refine ⟨?_,?_⟩
  · intro r hr
    apply (ht.1 r hr).congr
    exact (he r hr).mono (fun z hz=>congrArg (fun x : ℝ=>x^2) hz)
  · apply ht.2.congr'
    filter_upwards [eventually_ge_atTop (1:ℝ)] with r hr
    exact integral_congr_ae ((he r hr).mono (fun z hz=>congrArg (fun x : ℝ=>x^2) hz))

end
end JinWishart
#print axioms JinWishart.actualCorrelatedMatrixLogDet_offset_mean_square
