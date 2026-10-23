import JinWishartFormalization.PositiveSpectrumFatouDivergence
import JinWishartFormalization.ActualPositiveSecondCoefficient

/-! Critical generic-square model has divergent scaled expected first
coefficient. Every finite-scale real expectation is finite; the function
tends to atTop, not a Bochner integral assigned infinity. Codex.
Controls seed2026102244:10 calibrated Exp1/deterministic controls.
[需人工审查] Fatou, countably generated filter, AE rank and source/model. -/
open Matrix Module MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace JinWishart
noncomputable section

private theorem criticalOffsetEq {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (t : ℝ) (ht : 0<t) (z : ComplexSample (m := m) (n := p))
    (hz : (complexSampleMatrix z*B+M).rank=m) :
    (∑ j,positiveModeOffsetError (actualCorrelatedEigenvalue B M j z) t)=
      actualCorrelatedMatrixLogDet B M t z-(m : ℝ)*Real.log t-
        ∑ j,positiveSpectrumLog (actualCorrelatedEigenvalue B M j z) := by
  classical
  have hc := gram_positive_modes_eq_rank (complexSampleMatrix z*B+M)
  change (∑ j,if 0<actualCorrelatedEigenvalue B M j z then (1 : ℝ) else 0)=_ at hc
  rw [hz] at hc
  have hC : (∑ j,Real.log (1+t*actualCorrelatedEigenvalue B M j z))=
      actualCorrelatedMatrixLogDet B M t z := by
    simpa only [finiteSpectrumLogDet] using
      (actualCorrelatedMatrixLogDet_eq_spectral B M t ht.le z).symm
  unfold positiveModeOffsetError
  rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,← Finset.sum_mul,hc,hC]

theorem actualCorrelatedMatrixLogDet_critical_scaled_offset_tendsto_atTop {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (hr : m=(Matrix.fromRows B M).rank) (hm : 0<m) (hb : 0<B.rank)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=m) :
    let S := fun z : ComplexSample (m := m) (n := p) =>
      ∑ j,positiveSpectrumLog (actualCorrelatedEigenvalue B M j z)
    Tendsto (fun t : ℝ => t*((∫ z,actualCorrelatedMatrixLogDet B M t z ∂stdGaussian _)-
      (m : ℝ)*Real.log t-(∫ z,S z ∂stdGaussian _))) atTop atTop := by
  classical
  intro S
  let μ := stdGaussian (ComplexSample (m := m) (n := p))
  let L := fun z : ComplexSample (m := m) (n := p) => ∑ j,(actualCorrelatedEigenvalue B M j z)⁻¹
  have hMinInv := actual_singular_positive_inverse_realMoment_lintegral_eq_top
    B M hr (by simpa using hm) hb (by omega) i (by simpa using hi) (1 : ℝ) (by simp)
  have hMinTop : (∫⁻ z,ENNReal.ofReal ((actualCorrelatedEigenvalue B M i z)⁻¹) ∂μ)=⊤ := by
    simpa only [Real.rpow_one] using hMinInv
  have hLTop : (∫⁻ z,ENNReal.ofReal (L z) ∂μ)=⊤ := by
    apply top_unique
    rw [← hMinTop]
    apply lintegral_mono
    intro z
    apply ENNReal.ofReal_le_ofReal
    exact Finset.single_le_sum (fun j _ => inv_nonneg.mpr
      (actualCorrelatedEigenvalue_nonneg B M j z)) (Finset.mem_univ i)
  have hGen := positiveSpectrum_scaled_offset_lintegral_tendsto_top μ (actualCorrelatedEigenvalue B M)
    (measurable_actualCorrelatedEigenvalue B M)
    (fun j => ae_of_all _ (actualCorrelatedEigenvalue_nonneg B M j)) hLTop
  have hRank := actualCorrelatedRank_eq_generic_ae B M
  rw [← matrix_fromRows_rank_eq B M,← hr,Nat.min_self] at hRank
  have hS := integrable_actualCorrelated_positive_log_sum B M
  change Integrable S μ at hS
  apply ENNReal.tendsto_ofReal_nhds_top.mp
  apply hGen.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have ht0 : 0<t := zero_lt_one.trans_le ht
  let F := fun z : ComplexSample (m := m) (n := p) =>
    t*(actualCorrelatedMatrixLogDet B M t z-(m : ℝ)*Real.log t-S z)
  have hC : Integrable (actualCorrelatedMatrixLogDet B M t) μ :=
    integrable_actualCorrelatedMatrixLogDet B M t ht0.le
  have hFI : Integrable F μ := ((hC.sub (integrable_const _)).sub hS).const_mul t
  have hEq : (fun z => t*(∑ j,positiveModeOffsetError (actualCorrelatedEigenvalue B M j z) t))=ᵐ[μ]F := by
    filter_upwards [hRank] with z hz
    rw [criticalOffsetEq B M t ht0 z hz]
  have hNN : 0≤ᵐ[μ]F := by
    filter_upwards [hRank] with z hz
    change 0≤t*(actualCorrelatedMatrixLogDet B M t z-(m : ℝ)*Real.log t-S z)
    rw [← criticalOffsetEq B M t ht0 z hz]
    exact mul_nonneg ht0.le (Finset.sum_nonneg (fun j _ =>
      (positiveModeOffsetError_nonneg_le_inverse _ t (actualCorrelatedEigenvalue_nonneg B M j z) ht0).1))
  calc
    _=(∫⁻ z,ENNReal.ofReal (F z) ∂μ) :=
      lintegral_congr_ae (hEq.mono (fun z hz => congrArg ENNReal.ofReal hz))
    _=ENNReal.ofReal (∫ z,F z ∂μ) := (ofReal_integral_eq_lintegral_ofReal hFI hNN).symm
    _=_ := by
      dsimp only [F]
      rw [integral_const_mul,
        integral_sub (f := fun z => actualCorrelatedMatrixLogDet B M t z-(m : ℝ)*Real.log t)
          (g := S) (hC.sub (integrable_const _)) hS,
        integral_sub (f := actualCorrelatedMatrixLogDet B M t)
          (g := fun _ => (m : ℝ)*Real.log t) hC (integrable_const _)]
      simp [μ]

end
end JinWishart
#print axioms JinWishart.actualCorrelatedMatrixLogDet_critical_scaled_offset_tendsto_atTop
