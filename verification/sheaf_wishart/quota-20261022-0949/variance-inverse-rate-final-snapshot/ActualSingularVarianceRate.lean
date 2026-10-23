import JinWishartFormalization.VarianceMeanSquareBound
import JinWishartFormalization.ActualSingularOffsetRate
import JinWishartFormalization.ActualSingularLogDetVarianceLimit

/-! Explicit actual full-logdet variance difference rate under inverse-square
integrability. Codex. Controls seed2026102240 plus prior offset807 reused.
[需人工审查] Centering, L2/integral semantics and physical model mapping.
No independence of offset and limit is assumed. -/
open Matrix Module MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

theorem actualCorrelatedMatrixLogDet_variance_inverse_bound {m p n r : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (hr : r=(Matrix.fromRows B M).rank) (hR : 0<min m r)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=min m r)
    (hMoment : B.rank=0 ∨ r-B.rank=m ∨ (2 : ℝ)<((max m r-min m r+1 : ℕ) : ℝ)) :
    let S := fun z : ComplexSample (m := m) (n := p) =>
      ∑ j,positiveSpectrumLog (actualCorrelatedEigenvalue B M j z)
    let K : ℝ := ∫ z,((actualCorrelatedEigenvalue B M i z)⁻¹)^2 ∂stdGaussian _
    ∀ t : ℝ,1≤t →
      |variance (actualCorrelatedMatrixLogDet B M t) (stdGaussian _)-variance S (stdGaussian _)|
        ≤((n : ℝ)*t⁻¹)^2*K+2*((n : ℝ)*t⁻¹)*Real.sqrt K*Real.sqrt (variance S (stdGaussian _)) := by
  intro S K t ht
  let μ := stdGaussian (ComplexSample (m := m) (n := p))
  let R : ℝ := (min m r : ℕ)
  let U := fun z : ComplexSample (m := m) (n := p) =>
    actualCorrelatedMatrixLogDet B M t z-R*Real.log t
  have hS := integrable_actualCorrelated_positive_log_sum B M
  have hQ := integrable_actualCorrelated_positive_log_sum_sq B M
  change Integrable S μ at hS
  change Integrable (fun z => (S z)^2) μ at hQ
  have hSM : MemLp S 2 μ := (memLp_two_iff_integrable_sq hS.aestronglyMeasurable).2 hQ
  have hUM : MemLp U 2 μ := by
    have hh := (actualCorrelatedMatrixLogDet_offset_second_moment B M).1 t ht
    simpa only [← hr] using hh
  have hVar : variance U μ=variance (actualCorrelatedMatrixLogDet B M t) μ :=
    variance_sub_const
      (integrable_actualCorrelatedMatrixLogDet B M t (zero_le_one.trans ht)).aestronglyMeasurable (R*Real.log t)
  have hh := variance_difference_le_mean_square μ U S hUM hSM
  rw [hVar] at hh
  have hMSE := (actualCorrelatedMatrixLogDet_offset_mean_square_inverse_bound
    B M hr hR i hi hMoment).2 t ht
  change (∫ z,(U z-S z)^2 ∂μ)≤((n : ℝ)*t⁻¹)^2*K at hMSE
  have hroot := Real.sqrt_le_sqrt hMSE
  have hvnon := Real.sqrt_nonneg (variance S μ)
  have hc : 0≤(n : ℝ)*t⁻¹ := by positivity
  have hsqrt : Real.sqrt (((n : ℝ)*t⁻¹)^2*K)=((n : ℝ)*t⁻¹)*Real.sqrt K := by
    rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_nonneg hc]
  calc
    _ ≤ (∫ z,(U z-S z)^2 ∂μ)+
        2*Real.sqrt (∫ z,(U z-S z)^2 ∂μ)*Real.sqrt (variance S μ) := hh
    _ ≤ ((n : ℝ)*t⁻¹)^2*K+
        2*Real.sqrt (((n : ℝ)*t⁻¹)^2*K)*Real.sqrt (variance S μ) := by nlinarith
    _ = _ := by rw [hsqrt];ring

end
end JinWishart
#print axioms JinWishart.actualCorrelatedMatrixLogDet_variance_inverse_bound
