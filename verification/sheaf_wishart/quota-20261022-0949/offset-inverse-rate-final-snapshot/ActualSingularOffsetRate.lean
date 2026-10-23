import JinWishartFormalization.FiniteSpectrumOffsetInverseRate
import JinWishartFormalization.ActualSingularInverseClassification
import JinWishartFormalization.ActualSingularOffsetL2

/-! Quantitative mean-square full-logdet offset bound when the minimum-positive
inverse second moment is finite. Codex. Controls seed2026102239 reused.
[需人工审查] AE rank, spectral identity, integral domination and model mapping.
No inverse-square or O(r^-2) claim is made at its critical threshold. -/
open Matrix Module MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

theorem actualCorrelatedMatrixLogDet_offset_mean_square_inverse_bound {m p n r : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (hr : r=(Matrix.fromRows B M).rank) (hR : 0<min m r)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=min m r)
    (hMoment : B.rank=0 ∨ r-B.rank=m ∨ (2 : ℝ)<((max m r-min m r+1 : ℕ) : ℝ)) :
    let R : ℝ := (min m r : ℕ)
    let S := fun z : ComplexSample (m := m) (n := p) =>
      ∑ j,positiveSpectrumLog (actualCorrelatedEigenvalue B M j z)
    Integrable (fun z => ((actualCorrelatedEigenvalue B M i z)⁻¹)^2) (stdGaussian _) ∧
      ∀ t : ℝ,1≤t →
        (∫ z,(actualCorrelatedMatrixLogDet B M t z-R*Real.log t-S z)^2 ∂stdGaussian _)
          ≤((n : ℝ)*t⁻¹)^2*(∫ z,((actualCorrelatedEigenvalue B M i z)⁻¹)^2 ∂stdGaussian _) := by
  classical
  intro R S
  have hIq := (actual_singular_positive_inverse_realMoment_integrable_iff
    B M hr hR i hi (2 : ℝ) (by norm_num)).mpr hMoment
  have hI : Integrable (fun z => ((actualCorrelatedEigenvalue B M i z)⁻¹)^2)
      (stdGaussian (ComplexSample (m := m) (n := p))) := by
    simpa only [Real.rpow_two] using hIq
  have hR' : 0<min m (Matrix.fromRows B M).rank := by rwa [← hr]
  obtain ⟨i0,hi0,hmi,hMin⟩ := exists_actualCorrelated_smallest_positive_coordinate B M hR'
  have he : i=i0 := Fin.ext (by rw [← hr] at hi0;omega)
  subst i0
  refine ⟨hI,?_⟩
  intro t ht
  have ht0 : 0<t := zero_lt_one.trans_le ht
  have hErrI : Integrable (fun z =>
      (actualCorrelatedMatrixLogDet B M t z-R*Real.log t-S z)^2) (stdGaussian _) := by
    have hh := (actualCorrelatedMatrixLogDet_offset_mean_square B M).1 t ht
    simpa only [← hr] using hh
  have hBound : ∀ᵐ z ∂stdGaussian (ComplexSample (m := m) (n := p)),
      (actualCorrelatedMatrixLogDet B M t z-R*Real.log t-S z)^2≤
        ((n : ℝ)*t⁻¹)^2*((actualCorrelatedEigenvalue B M i z)⁻¹)^2 := by
    filter_upwards [hMin,actualCorrelatedRank_eq_generic_ae B M] with z hz hzr
    have hcount := gram_positive_modes_eq_rank (complexSampleMatrix z*B+M)
    change (∑ j,if 0<actualCorrelatedEigenvalue B M j z then (1 : ℝ) else 0)=_ at hcount
    have hRank : ((complexSampleMatrix z*B+M).rank : ℝ)=R := by
      rw [hzr,← matrix_fromRows_rank_eq,← hr]
    have hCountR := hcount.trans hRank
    have hC : (∑ j,Real.log (1+t*actualCorrelatedEigenvalue B M j z))=
        actualCorrelatedMatrixLogDet B M t z := by
      simpa only [finiteSpectrumLogDet] using
        (actualCorrelatedMatrixLogDet_eq_spectral B M t ht0.le z).symm
    have hE : (∑ j,positiveModeOffsetError (actualCorrelatedEigenvalue B M j z) t)=
        actualCorrelatedMatrixLogDet B M t z-R*Real.log t-S z := by
      unfold positiveModeOffsetError
      rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,← Finset.sum_mul,hCountR,hC]
    have hb := finiteSpectrumOffsetError_nonneg_le_min_inverse
      (fun j => actualCorrelatedEigenvalue B M j z)
      (fun j => actualCorrelatedEigenvalue_nonneg B M j z)
      (actualCorrelatedEigenvalue B M i z) t hz.1 ht0 hz.2
    simp only [Fintype.card_fin,hE] at hb
    have hh := pow_le_pow_left₀ hb.1 hb.2 2
    simpa only [mul_pow] using hh
  have hh := integral_mono_ae hErrI (hI.const_mul (((n : ℝ)*t⁻¹)^2)) hBound
  rwa [integral_const_mul] at hh

end
end JinWishart
#print axioms JinWishart.actualCorrelatedMatrixLogDet_offset_mean_square_inverse_bound
