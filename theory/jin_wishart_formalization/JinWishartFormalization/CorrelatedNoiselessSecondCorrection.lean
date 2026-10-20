import JinWishartFormalization.CorrelatedNoiselessFirstCorrection
import JinWishartFormalization.NoiselessRowSecondCorrection

/-! Actual second inverse-trace coefficient with a positive cubic remainder.
Codex, fixed noiseless-surjective B/M. No SNR-varying parameter uniformity.
[需人工审查] Probability integrability, expectation linearity, asymptotics and model.
-/
open Matrix Module MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace JinWishart
noncomputable section

theorem actualCorrelatedRow_expectedSecondCorrection_bounds {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (hm : 0<m)
    (hs : finrank ℂ (LinearMap.range (M.mulVecLin.domRestrict (LinearMap.ker B.mulVecLin)))=m) :
    ∃ δ : ℝ, 0<δ ∧ ∀ r : ℝ, 0<r →
      0≤r^2*actualCorrelatedExpectedRowOffsetError B M r-
        r*(∫ z, actualCorrelatedRowInverseTracePow B M 1 z ∂stdGaussian _)+
          (∫ z, actualCorrelatedRowInverseTracePow B M 2 z ∂stdGaussian _)/2 ∧
      r^2*actualCorrelatedExpectedRowOffsetError B M r-
        r*(∫ z, actualCorrelatedRowInverseTracePow B M 1 z ∂stdGaussian _)+
          (∫ z, actualCorrelatedRowInverseTracePow B M 2 z ∂stdGaussian _)/2 ≤ (m:ℝ)/(3*r*δ^3) := by
  obtain ⟨δ,hδ,hfloor⟩ := correlated_rowGram_uniform_floor B M hm hs
  refine ⟨δ,hδ,fun r hr => ?_⟩
  let E := fun z : ComplexSample (m := m) (n := p) =>
    actualCorrelatedMatrixLogDet B M r z-(m:ℝ)*Real.log r-actualCorrelatedRowLogDet B M z
  have hC := integrable_actualCorrelatedMatrixLogDet B M r hr.le
  have hL := integrable_actualCorrelatedRowLogDet_of_noiseless_surjective B M hm hs
  have hE : Integrable E (stdGaussian _) := (hC.sub (integrable_const _)).sub hL
  have hI1 := integrable_actualCorrelatedRowInverseTracePow B M hm hs 1
  have hI2 := integrable_actualCorrelatedRowInverseTracePow B M hm hs 2
  have he : (∫ z, E z ∂stdGaussian _)=actualCorrelatedExpectedRowOffsetError B M r := by
    dsimp only [E,actualCorrelatedExpectedRowOffsetError]
    rw [integral_sub (f := fun z => actualCorrelatedMatrixLogDet B M r z-(m:ℝ)*Real.log r)
      (g := actualCorrelatedRowLogDet B M) (hC.sub (integrable_const _)) hL,
      integral_sub (f := actualCorrelatedMatrixLogDet B M r) (g := fun _ => (m:ℝ)*Real.log r)
        hC (integrable_const _)]
    simp
  let F := fun z => r^2*E z-r*actualCorrelatedRowInverseTracePow B M 1 z+
    actualCorrelatedRowInverseTracePow B M 2 z/2
  have hF : Integrable F (stdGaussian _) :=
    ((hE.const_mul (r^2)).sub (hI1.const_mul r)).add (hI2.div_const 2)
  have hFe : (∫ z, F z ∂stdGaussian _)=r^2*actualCorrelatedExpectedRowOffsetError B M r-
      r*(∫ z, actualCorrelatedRowInverseTracePow B M 1 z ∂stdGaussian _)+
        (∫ z, actualCorrelatedRowInverseTracePow B M 2 z ∂stdGaussian _)/2 := by
    dsimp only [F]
    rw [integral_add (f := fun z => r^2*E z-r*actualCorrelatedRowInverseTracePow B M 1 z)
      (g := fun z => actualCorrelatedRowInverseTracePow B M 2 z/2)
      ((hE.const_mul _).sub (hI1.const_mul _)) (hI2.div_const 2),
      integral_sub (f := fun z => r^2*E z) (g := fun z => r*actualCorrelatedRowInverseTracePow B M 1 z)
        (hE.const_mul _) (hI1.const_mul _),integral_div,integral_const_mul,integral_const_mul,he]
  have hb : ∀ z, 0≤F z-0-0 ∧ F z-0-0≤(m:ℝ)/(3*r*δ^3) := by
    intro z
    simpa only [F,E,sub_zero,actualCorrelatedRowInverseTracePow,pow_one,
      actualCorrelatedMatrixLogDet,actualCorrelatedRowLogDet] using
      rowLogDet_second_correction_bounds (complexSampleMatrix z*B+M) hm δ r hδ
        (hfloor (complexSampleMatrix z)) hr
  have h := integral_offset_remainder_bounds (stdGaussian _) F (fun _ => 0)
    hF (integrable_const 0) 0 ((m:ℝ)/(3*r*δ^3)) hb
  simpa only [integral_zero,sub_zero,hFe] using h

theorem actualCorrelatedRow_expectedSecondCorrection_tendsto {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (hm : 0<m)
    (hs : finrank ℂ (LinearMap.range (M.mulVecLin.domRestrict (LinearMap.ker B.mulVecLin)))=m) :
    Tendsto (fun r : ℝ => r^2*actualCorrelatedExpectedRowOffsetError B M r-
      r*(∫ z, actualCorrelatedRowInverseTracePow B M 1 z ∂stdGaussian _)) atTop
      (𝓝 (-(∫ z, actualCorrelatedRowInverseTracePow B M 2 z ∂stdGaussian _)/2)) := by
  obtain ⟨δ,hδ,hb⟩ := actualCorrelatedRow_expectedSecondCorrection_bounds B M hm hs
  apply tendsto_offset_of_inverse_bound _ _ ((m:ℝ)/(3*δ^3))
  intro r hr
  convert hb r hr using 1 <;> ring

end
end JinWishart
#print axioms JinWishart.actualCorrelatedRow_expectedSecondCorrection_bounds
#print axioms JinWishart.actualCorrelatedRow_expectedSecondCorrection_tendsto
