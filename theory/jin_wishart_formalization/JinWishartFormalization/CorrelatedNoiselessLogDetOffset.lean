import JinWishartFormalization.NoiselessRowLogDetError
import JinWishartFormalization.BoundedOffsetExpectation
import JinWishartFormalization.CorrelatedLogDetLowScale

/-! Actual Gaussian ROW logdet offset in the noiseless-surjective regime.
Codex. Fixed B,M; natural logs; ROW Gram XX^H even when column Gram is singular.
[需人工审查] Measurability, probability integrals, uniform squeeze and model correspondence.
-/
open Matrix Module MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace JinWishart
noncomputable section

def actualCorrelatedRowLogDet {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (z : ComplexSample (m := m) (n := p)) : ℝ :=
  Real.log ((complexGram (complexSampleMatrix z*B+M)ᴴ).det.re)

set_option maxHeartbeats 1000000 in
theorem measurable_actualCorrelatedRowLogDet {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) :
    Measurable (actualCorrelatedRowLogDet B M) := by
  have hX : Continuous (fun z : ComplexSample (m := m) (n := p) => complexSampleMatrix z*B+M) := by
    apply continuous_matrix
    intro i j
    simp only [Matrix.add_apply,Matrix.mul_apply,complexSampleMatrix]
    fun_prop
  have hG : Continuous (fun z : ComplexSample (m := m) (n := p) =>
      complexGram (complexSampleMatrix z*B+M)ᴴ) := by
    simp only [complexGram,Matrix.conjTranspose_conjTranspose]
    fun_prop
  exact Real.measurable_log.comp (Complex.continuous_re.comp hG.matrix_det).measurable

theorem integrable_actualCorrelatedRowLogDet_of_noiseless_surjective {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (hm : 0<m)
    (hs : finrank ℂ (LinearMap.range (M.mulVecLin.domRestrict (LinearMap.ker B.mulVecLin)))=m) :
    Integrable (actualCorrelatedRowLogDet B M) (stdGaussian _) := by
  obtain ⟨δ,hδ,hfloor⟩ := correlated_rowGram_uniform_floor B M hm hs
  apply integrable_offset_of_bounded_remainder (stdGaussian _)
    (actualCorrelatedMatrixLogDet B M 1) (actualCorrelatedRowLogDet B M)
    (integrable_actualCorrelatedMatrixLogDet B M 1 (by norm_num))
    (measurable_actualCorrelatedRowLogDet B M) ((m:ℝ)/δ)
  intro z
  simpa only [actualCorrelatedMatrixLogDet,actualCorrelatedRowLogDet,Real.log_one,
    mul_zero,sub_zero,one_mul] using
    rowLogDet_offset_error_bounds (complexSampleMatrix z*B+M) hm δ 1 hδ
      (hfloor (complexSampleMatrix z)) (by norm_num)

theorem actualCorrelatedRow_expectedOffset_bounds {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (hm : 0<m)
    (hs : finrank ℂ (LinearMap.range (M.mulVecLin.domRestrict (LinearMap.ker B.mulVecLin)))=m) :
    ∃ δ : ℝ, 0<δ ∧ ∀ r : ℝ, 0<r →
      0≤(∫ z, actualCorrelatedMatrixLogDet B M r z ∂stdGaussian _)-(m:ℝ)*Real.log r-
        (∫ z, actualCorrelatedRowLogDet B M z ∂stdGaussian _) ∧
      (∫ z, actualCorrelatedMatrixLogDet B M r z ∂stdGaussian _)-(m:ℝ)*Real.log r-
        (∫ z, actualCorrelatedRowLogDet B M z ∂stdGaussian _) ≤ (m:ℝ)/(r*δ) := by
  obtain ⟨δ,hδ,hfloor⟩ := correlated_rowGram_uniform_floor B M hm hs
  refine ⟨δ,hδ,fun r hr => ?_⟩
  apply integral_offset_remainder_bounds (stdGaussian _)
    (actualCorrelatedMatrixLogDet B M r) (actualCorrelatedRowLogDet B M)
    (integrable_actualCorrelatedMatrixLogDet B M r hr.le)
    (integrable_actualCorrelatedRowLogDet_of_noiseless_surjective B M hm hs)
  intro z
  exact rowLogDet_offset_error_bounds (complexSampleMatrix z*B+M) hm δ r hδ
    (hfloor (complexSampleMatrix z)) hr

theorem actualCorrelatedRow_expectedOffset_tendsto {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (hm : 0<m)
    (hs : finrank ℂ (LinearMap.range (M.mulVecLin.domRestrict (LinearMap.ker B.mulVecLin)))=m) :
    Tendsto (fun r : ℝ => (∫ z, actualCorrelatedMatrixLogDet B M r z ∂stdGaussian _)-
      (m:ℝ)*Real.log r) atTop
      (𝓝 (∫ z, actualCorrelatedRowLogDet B M z ∂stdGaussian _)) := by
  obtain ⟨δ,hδ,hb⟩ := actualCorrelatedRow_expectedOffset_bounds B M hm hs
  apply tendsto_offset_of_inverse_bound _ _ ((m:ℝ)/δ)
  intro r hr
  simpa only [div_div, mul_comm δ r] using hb r hr

end
end JinWishart
#print axioms JinWishart.measurable_actualCorrelatedRowLogDet
#print axioms JinWishart.integrable_actualCorrelatedRowLogDet_of_noiseless_surjective
#print axioms JinWishart.actualCorrelatedRow_expectedOffset_bounds
#print axioms JinWishart.actualCorrelatedRow_expectedOffset_tendsto
