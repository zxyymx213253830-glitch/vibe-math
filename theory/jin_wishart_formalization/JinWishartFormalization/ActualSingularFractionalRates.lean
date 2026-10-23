import JinWishartFormalization.FiniteSpectrumFractionalOffset
import JinWishartFormalization.ActualSingularVarianceRate

/-! Fractional offset and variance rates, including subcritical square models.
Codex. Controls seed2026102241:1323 checks, calibrated Gamma1 finite fractional
inverse moments; not endpoint asymptotics. [需人工审查] Source, AE rank/index,
real powers, integral/variance meaning and paper interpretation. -/
open Matrix Module MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

theorem actualCorrelatedMatrixLogDet_offset_fractional_mean_square_bound {m p n r : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (hr : r=(Matrix.fromRows B M).rank) (hR : 0<min m r)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=min m r)
    (α : ℝ) (hα : 0<α) (hα1 : α≤1)
    (hMoment : B.rank=0 ∨ r-B.rank=m ∨ 2*α<((max m r-min m r+1 : ℕ) : ℝ)) :
    let R : ℝ := (min m r : ℕ)
    let S := fun z : ComplexSample (m := m) (n := p) =>
      ∑ j,positiveSpectrumLog (actualCorrelatedEigenvalue B M j z)
    Integrable (fun z => ((actualCorrelatedEigenvalue B M i z)⁻¹)^(2*α)) (stdGaussian _) ∧
      ∀ t : ℝ,1≤t →
        (∫ z,(actualCorrelatedMatrixLogDet B M t z-R*Real.log t-S z)^2 ∂stdGaussian _)
          ≤((n : ℝ)*α⁻¹*(t⁻¹)^α)^2*
            (∫ z,((actualCorrelatedEigenvalue B M i z)⁻¹)^(2*α) ∂stdGaussian _) := by
  classical
  intro R S
  have hI := (actual_singular_positive_inverse_realMoment_integrable_iff
    B M hr hR i hi (2*α) (by positivity)).mpr hMoment
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
        ((n : ℝ)*α⁻¹*(t⁻¹)^α)^2*((actualCorrelatedEigenvalue B M i z)⁻¹)^(2*α) := by
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
    have hb := finiteSpectrumOffsetError_fractional_min_bound
      (fun j => actualCorrelatedEigenvalue B M j z)
      (fun j => actualCorrelatedEigenvalue_nonneg B M j z)
      (actualCorrelatedEigenvalue B M i z) t α hz.1 ht0 hα hα1 hz.2
    simp only [Fintype.card_fin,hE] at hb
    have hpow : (((actualCorrelatedEigenvalue B M i z)⁻¹)^α)^2=
        ((actualCorrelatedEigenvalue B M i z)⁻¹)^(2*α) := by
      rw [← Real.rpow_mul_natCast (inv_nonneg.mpr hz.1.le) α 2]
      congr 1
      ring
    have hh := pow_le_pow_left₀ hb.1 hb.2 2
    simpa only [mul_pow,hpow] using hh
  have hh := integral_mono_ae hErrI (hI.const_mul (((n : ℝ)*α⁻¹*(t⁻¹)^α)^2)) hBound
  rwa [integral_const_mul] at hh

theorem actualCorrelatedMatrixLogDet_variance_fractional_bound {m p n r : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (hr : r=(Matrix.fromRows B M).rank) (hR : 0<min m r)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=min m r)
    (α : ℝ) (hα : 0<α) (hα1 : α≤1)
    (hMoment : B.rank=0 ∨ r-B.rank=m ∨ 2*α<((max m r-min m r+1 : ℕ) : ℝ)) :
    let S := fun z : ComplexSample (m := m) (n := p) =>
      ∑ j,positiveSpectrumLog (actualCorrelatedEigenvalue B M j z)
    let K : ℝ := ∫ z,((actualCorrelatedEigenvalue B M i z)⁻¹)^(2*α) ∂stdGaussian _
    ∀ t : ℝ,1≤t →
      |variance (actualCorrelatedMatrixLogDet B M t) (stdGaussian _)-variance S (stdGaussian _)|
        ≤((n : ℝ)*α⁻¹*(t⁻¹)^α)^2*K+
          2*((n : ℝ)*α⁻¹*(t⁻¹)^α)*Real.sqrt K*Real.sqrt (variance S (stdGaussian _)) := by
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
  have hMSE := (actualCorrelatedMatrixLogDet_offset_fractional_mean_square_bound
    B M hr hR i hi α hα hα1 hMoment).2 t ht
  change (∫ z,(U z-S z)^2 ∂μ)≤((n : ℝ)*α⁻¹*(t⁻¹)^α)^2*K at hMSE
  have hroot := Real.sqrt_le_sqrt hMSE
  have hvnon := Real.sqrt_nonneg (variance S μ)
  have hc : 0≤(n : ℝ)*α⁻¹*(t⁻¹)^α := by positivity
  have hsqrt : Real.sqrt (((n : ℝ)*α⁻¹*(t⁻¹)^α)^2*K)=
      ((n : ℝ)*α⁻¹*(t⁻¹)^α)*Real.sqrt K := by
    rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_of_nonneg hc]
  calc
    _ ≤ (∫ z,(U z-S z)^2 ∂μ)+
        2*Real.sqrt (∫ z,(U z-S z)^2 ∂μ)*Real.sqrt (variance S μ) := hh
    _ ≤ ((n : ℝ)*α⁻¹*(t⁻¹)^α)^2*K+
        2*Real.sqrt (((n : ℝ)*α⁻¹*(t⁻¹)^α)^2*K)*Real.sqrt (variance S μ) := by nlinarith
    _ = _ := by rw [hsqrt];ring

end
end JinWishart
#print axioms JinWishart.actualCorrelatedMatrixLogDet_offset_fractional_mean_square_bound
#print axioms JinWishart.actualCorrelatedMatrixLogDet_variance_fractional_bound
