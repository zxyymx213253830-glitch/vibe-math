import JinWishartFormalization.CorrelatedRowInverseTrace
import JinWishartFormalization.NoiselessRowFirstCorrection

/-! Actual expected inverse-trace first correction, with a deterministic rate.
Codex. Fixed noiseless-surjective model; natural log; no channel coding assertion.
[需人工审查] Integrability/linearity/squeeze and model correspondence.
-/
open Matrix Module MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace JinWishart
noncomputable section

def actualCorrelatedExpectedRowOffsetError {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (r : ℝ) : ℝ :=
  (∫ z, actualCorrelatedMatrixLogDet B M r z ∂stdGaussian _)-(m:ℝ)*Real.log r-
    (∫ z, actualCorrelatedRowLogDet B M z ∂stdGaussian _)

theorem actualCorrelatedRow_expectedFirstCorrection_bounds {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (hm : 0<m)
    (hs : finrank ℂ (LinearMap.range (M.mulVecLin.domRestrict (LinearMap.ker B.mulVecLin)))=m) :
    ∃ δ : ℝ, 0<δ ∧ ∀ r : ℝ, 0<r →
      0≤(∫ z, actualCorrelatedRowInverseTracePow B M 1 z ∂stdGaussian _)-
        r*actualCorrelatedExpectedRowOffsetError B M r ∧
      (∫ z, actualCorrelatedRowInverseTracePow B M 1 z ∂stdGaussian _)-
        r*actualCorrelatedExpectedRowOffsetError B M r ≤ (m:ℝ)/(2*r*δ^2) := by
  obtain ⟨δ,hδ,hfloor⟩ := correlated_rowGram_uniform_floor B M hm hs
  refine ⟨δ,hδ,fun r hr => ?_⟩
  let E := fun z : ComplexSample (m := m) (n := p) =>
    actualCorrelatedMatrixLogDet B M r z-(m:ℝ)*Real.log r-actualCorrelatedRowLogDet B M z
  have hC := integrable_actualCorrelatedMatrixLogDet B M r hr.le
  have hL := integrable_actualCorrelatedRowLogDet_of_noiseless_surjective B M hm hs
  have hE : Integrable E (stdGaussian _) := (hC.sub (integrable_const _)).sub hL
  have he : (∫ z, E z ∂stdGaussian _)=actualCorrelatedExpectedRowOffsetError B M r := by
    dsimp only [E,actualCorrelatedExpectedRowOffsetError]
    rw [integral_sub (f := fun z => actualCorrelatedMatrixLogDet B M r z-(m:ℝ)*Real.log r)
      (g := actualCorrelatedRowLogDet B M) (hC.sub (integrable_const _)) hL,
      integral_sub (f := actualCorrelatedMatrixLogDet B M r) (g := fun _ => (m:ℝ)*Real.log r)
        hC (integrable_const _)]
    simp
  have hb (z : ComplexSample (m := m) (n := p)) :
      0≤actualCorrelatedRowInverseTracePow B M 1 z-0-r*E z ∧
      actualCorrelatedRowInverseTracePow B M 1 z-0-r*E z≤(m:ℝ)/(2*r*δ^2) := by
    simpa only [actualCorrelatedRowInverseTracePow,pow_one,sub_zero,E,
      actualCorrelatedMatrixLogDet,actualCorrelatedRowLogDet] using
      rowLogDet_first_correction_bounds (complexSampleMatrix z*B+M) hm δ r hδ
        (hfloor (complexSampleMatrix z)) hr
  have h := integral_offset_remainder_bounds (stdGaussian _)
    (actualCorrelatedRowInverseTracePow B M 1) (fun z => r*E z)
    (integrable_actualCorrelatedRowInverseTracePow B M hm hs 1) (hE.const_mul r)
    0 ((m:ℝ)/(2*r*δ^2)) hb
  simpa only [sub_zero,integral_const_mul,he] using h

theorem actualCorrelatedRow_expectedFirstCorrection_tendsto {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (hm : 0<m)
    (hs : finrank ℂ (LinearMap.range (M.mulVecLin.domRestrict (LinearMap.ker B.mulVecLin)))=m) :
    Tendsto (fun r : ℝ => r*actualCorrelatedExpectedRowOffsetError B M r) atTop
      (𝓝 (∫ z, actualCorrelatedRowInverseTracePow B M 1 z ∂stdGaussian _)) := by
  obtain ⟨δ,hδ,hb⟩ := actualCorrelatedRow_expectedFirstCorrection_bounds B M hm hs
  let L := ∫ z, actualCorrelatedRowInverseTracePow B M 1 z ∂stdGaussian _
  have ht : Tendsto (fun r : ℝ => L-r*actualCorrelatedExpectedRowOffsetError B M r) atTop (𝓝 0) := by
    have hK : Tendsto (fun r : ℝ => ((m:ℝ)/(2*δ^2))/r) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    apply squeeze_zero' ?_ ?_ hK
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
      exact (hb r hr).1
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
      convert (hb r hr).2 using 1 <;> ring
  have hs := (tendsto_const_nhds : Tendsto (fun _ : ℝ => L) atTop (𝓝 L)).sub ht
  simpa only [sub_sub_cancel,sub_zero] using hs

end
end JinWishart
#print axioms JinWishart.actualCorrelatedRow_expectedFirstCorrection_bounds
#print axioms JinWishart.actualCorrelatedRow_expectedFirstCorrection_tendsto
