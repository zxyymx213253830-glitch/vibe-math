import JinWishartFormalization.PositiveSpectrumSecondFatou

/-! Inverse2-critical fixed model: finite first coefficient, divergent scaled
second gap. Every finite-scale real expectation is finite. Codex.
Seed2026102245:48 Gamma2/finite controls, not divergence proof.
[需人工审查] Fatou, original Gaussian source, AE rank, integrability and linearity.
No optimal critical logarithmic coefficient or ordinary singular inverse claimed. -/
open Matrix Module MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace JinWishart
noncomputable section

private theorem criticalSecondOffsetEq {m p n r : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (t : ℝ) (ht : 0<t) (z : ComplexSample (m := m) (n := p))
    (hz : (complexSampleMatrix z*B+M).rank=min m r) :
    (∑ j,positiveModeOffsetError (actualCorrelatedEigenvalue B M j z) t)=
      actualCorrelatedMatrixLogDet B M t z-(min m r : ℕ)*Real.log t-
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

private theorem criticalSecondModeNonneg (x t : ℝ) (hx : 0≤x) (ht : 0<t) :
    0≤t*(x⁻¹-t*positiveModeOffsetError x t) := by
  have hh := mul_le_mul_of_nonneg_left
    (positiveModeOffsetError_nonneg_le_inverse x t hx ht).2 ht.le
  rw [← mul_assoc,mul_inv_cancel₀ ht.ne',one_mul] at hh
  exact mul_nonneg ht.le (sub_nonneg.mpr hh)

theorem actualCorrelatedMatrixLogDet_critical_second_gap_tendsto_atTop {m p n r : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (hr : r=(Matrix.fromRows B M).rank) (hR : 0<min m r)
    (hb : 0<B.rank) (hcm : r-B.rank<m) (hk : max m r-min m r+1=2)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=min m r) :
    let S := fun z : ComplexSample (m := m) (n := p) =>
      ∑ j,positiveSpectrumLog (actualCorrelatedEigenvalue B M j z)
    let L := fun z : ComplexSample (m := m) (n := p) =>
      ∑ j,(actualCorrelatedEigenvalue B M j z)⁻¹
    Integrable L (stdGaussian _) ∧
      Tendsto (fun t : ℝ => t*((∫ z,L z ∂stdGaussian _)-
        t*((∫ z,actualCorrelatedMatrixLogDet B M t z ∂stdGaussian _)-
          (min m r : ℕ)*Real.log t-(∫ z,S z ∂stdGaussian _)))) atTop atTop := by
  classical
  intro S L
  let μ := stdGaussian (ComplexSample (m := m) (n := p))
  let Q := fun z : ComplexSample (m := m) (n := p) =>
    ∑ j,((actualCorrelatedEigenvalue B M j z)⁻¹)^2
  have hMoment1 : B.rank=0 ∨ r-B.rank=m ∨ (1 : ℝ)<((max m r-min m r+1 : ℕ) : ℝ) := by
    exact Or.inr (Or.inr (by rw [hk];norm_num))
  have hLI : Integrable L μ :=
    (actualCorrelatedMatrixLogDet_expected_positive_first_coefficient B M hr hR i hi hMoment1).1
  have hQm : Measurable Q := by
    apply Finset.measurable_sum
    intro j _
    exact (measurable_actualCorrelatedEigenvalue B M j).inv.pow_const 2
  have hQnon (z : ComplexSample (m := m) (n := p)) : 0≤Q z :=
    Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hQTop : (∫⁻ z,ENNReal.ofReal (Q z/2) ∂μ)=⊤ := by
    by_contra h
    have hHalfI : Integrable (fun z => Q z/2) μ :=
      (lintegral_ofReal_ne_top_iff_integrable (hQm.div_const 2).aestronglyMeasurable
        (ae_of_all _ (fun z => div_nonneg (hQnon z) (by norm_num)))).mp h
    have hQI : Integrable Q μ := by
      convert hHalfI.const_mul 2 using 1
      funext z
      ring
    have hMinI : Integrable (fun z => ((actualCorrelatedEigenvalue B M i z)⁻¹)^2) μ := by
      apply hQI.mono' ((measurable_actualCorrelatedEigenvalue B M i).inv.pow_const 2).aestronglyMeasurable
      apply ae_of_all
      intro z
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      change ((actualCorrelatedEigenvalue B M i z)⁻¹)^2≤
        ∑ j,((actualCorrelatedEigenvalue B M j z)⁻¹)^2
      exact Finset.single_le_sum (fun j _ => sq_nonneg ((actualCorrelatedEigenvalue B M j z)⁻¹))
        (Finset.mem_univ i)
    have hMinI' : Integrable (fun z => (actualCorrelatedEigenvalue B M i z)⁻¹^(2 : ℝ)) μ := by
      simpa only [Real.rpow_two] using hMinI
    rcases (actual_singular_positive_inverse_realMoment_integrable_iff B M hr hR i hi
      (2 : ℝ) (by norm_num)).mp hMinI' with hz|hz|hz
    · omega
    · omega
    · rw [hk] at hz
      norm_num at hz
  have hGen := positiveSpectrum_second_gap_lintegral_tendsto_top μ (actualCorrelatedEigenvalue B M)
    (measurable_actualCorrelatedEigenvalue B M)
    (fun j => ae_of_all _ (actualCorrelatedEigenvalue_nonneg B M j)) hQTop
  have hRank := actualCorrelatedRank_eq_generic_ae B M
  rw [← matrix_fromRows_rank_eq B M,← hr] at hRank
  have hS := integrable_actualCorrelated_positive_log_sum B M
  change Integrable S μ at hS
  refine ⟨hLI,?_⟩
  apply ENNReal.tendsto_ofReal_nhds_top.mp
  apply hGen.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have ht0 : 0<t := zero_lt_one.trans_le ht
  let F := fun z : ComplexSample (m := m) (n := p) =>
    t*(L z-t*(actualCorrelatedMatrixLogDet B M t z-(min m r : ℕ)*Real.log t-S z))
  have hC : Integrable (actualCorrelatedMatrixLogDet B M t) μ :=
    integrable_actualCorrelatedMatrixLogDet B M t ht0.le
  have hE : Integrable (fun z => actualCorrelatedMatrixLogDet B M t z-
      (min m r : ℕ)*Real.log t-S z) μ := (hC.sub (integrable_const _)).sub hS
  have hFI : Integrable F μ := (hLI.sub (hE.const_mul t)).const_mul t
  have hEq : (fun z => ∑ j,t*((actualCorrelatedEigenvalue B M j z)⁻¹-
      t*positiveModeOffsetError (actualCorrelatedEigenvalue B M j z) t))=ᵐ[μ]F := by
    filter_upwards [hRank] with z hz
    rw [← Finset.mul_sum,Finset.sum_sub_distrib,← Finset.mul_sum,
      criticalSecondOffsetEq B M t ht0 z hz]
  have hNN : 0≤ᵐ[μ]F := by
    filter_upwards [hEq] with z hz
    rw [← hz]
    exact Finset.sum_nonneg (fun j _ => criticalSecondModeNonneg _ t
      (actualCorrelatedEigenvalue_nonneg B M j z) ht0)
  calc
    _=(∫⁻ z,ENNReal.ofReal (F z) ∂μ) :=
      lintegral_congr_ae (hEq.mono (fun z hz => congrArg ENNReal.ofReal hz))
    _=ENNReal.ofReal (∫ z,F z ∂μ) := (ofReal_integral_eq_lintegral_ofReal hFI hNN).symm
    _=_ := by
      dsimp only [F]
      rw [integral_const_mul,
        integral_sub (f := L) (g := fun z => t*(actualCorrelatedMatrixLogDet B M t z-
          (min m r : ℕ)*Real.log t-S z)) hLI (hE.const_mul t),integral_const_mul,
        integral_sub (f := fun z => actualCorrelatedMatrixLogDet B M t z-(min m r : ℕ)*Real.log t)
          (g := S) (hC.sub (integrable_const _)) hS,
        integral_sub (f := actualCorrelatedMatrixLogDet B M t)
          (g := fun _ => (min m r : ℕ)*Real.log t) hC (integrable_const _)]
      simp [μ]

end
end JinWishart
#print axioms JinWishart.actualCorrelatedMatrixLogDet_critical_second_gap_tendsto_atTop
