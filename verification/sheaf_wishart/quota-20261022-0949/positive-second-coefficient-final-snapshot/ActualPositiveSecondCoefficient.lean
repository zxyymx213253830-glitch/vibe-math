import JinWishartFormalization.ActualPositiveFirstCoefficient
import JinWishartFormalization.NoiselessRowSecondCorrection

/-! Expected positive-spectrum second high-scale coefficient under inverse2
integrability. Codex. Controls seed2026102243:777 finite/Gamma3/4 checks.
[需人工审查] Dominated convergence, inverse powers, same-source model and
expectation linearity. Spectral reciprocal sums, not an ordinary singular inverse. -/
open Matrix Module MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace JinWishart
noncomputable section

private theorem modeEqLog (x t : ℝ) (hx : 0<x) (ht : 0<t) :
    positiveModeOffsetError x t=Real.log (1+(t*x)⁻¹) := by
  have htx : t*x≠0 := mul_ne_zero ht.ne' hx.ne'
  have harg : 0<1+(t*x)⁻¹ := by positivity
  have heq : 1+t*x=(t*x)*(1+(t*x)⁻¹) := by
    rw [mul_add,mul_one,mul_inv_cancel₀ htx]
    ring
  unfold positiveModeOffsetError positiveSpectrumLog
  rw [if_pos hx,one_mul,heq,Real.log_mul htx harg.ne',Real.log_mul ht.ne' hx.ne']
  simp only [if_pos hx]
  ring

private theorem modeSecondGapBound (x t : ℝ) (hx : 0≤x) (ht : 0<t) :
    0≤t*(x⁻¹-t*positiveModeOffsetError x t) ∧
      t*(x⁻¹-t*positiveModeOffsetError x t)≤(x⁻¹)^2/2 := by
  by_cases hp : 0<x
  · have hh := scaled_log_inverse_first_correction_bounds t x ht hp
    rw [← modeEqLog x t hp ht] at hh
    refine ⟨mul_nonneg ht.le hh.1,?_⟩
    have hu := mul_le_mul_of_nonneg_left hh.2 ht.le
    convert hu using 1 <;> field_simp [ht.ne',hp.ne'] <;> ring
  · have hz : x=0 := le_antisymm (le_of_not_gt hp) hx
    simp [hz,positiveModeOffsetError,positiveSpectrumLog]

theorem positiveModeOffsetError_second_scaled_tendsto (x : ℝ) (hx : 0≤x) :
    Tendsto (fun t : ℝ => t*(x⁻¹-t*positiveModeOffsetError x t)) atTop (𝓝 ((x⁻¹)^2/2)) := by
  by_cases hp : 0<x
  · have hb (t : ℝ) (ht : 0<t) :
        0≤(x⁻¹)^2/2-t*(x⁻¹-t*positiveModeOffsetError x t) ∧
          (x⁻¹)^2/2-t*(x⁻¹-t*positiveModeOffsetError x t)≤1/(3*t*x^3) := by
      have hh := scaled_log_inverse_second_correction_bounds t x ht hp
      rw [← modeEqLog x t hp ht] at hh
      have he : t^2*positiveModeOffsetError x t-t*x⁻¹+(x⁻¹)^2/2=
          (x⁻¹)^2/2-t*(x⁻¹-t*positiveModeOffsetError x t) := by ring
      rwa [he] at hh
    have hgap : Tendsto (fun t : ℝ => (x⁻¹)^2/2-t*(x⁻¹-t*positiveModeOffsetError x t))
        atTop (𝓝 0) := by
      have hK : Tendsto (fun t : ℝ => (1/(3*x^3))/t) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      apply squeeze_zero' ?_ ?_ hK
      · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
        exact (hb t ht).1
      · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
        convert (hb t ht).2 using 1 <;> field_simp [ht.ne',hp.ne'] <;> ring
    have hs := (tendsto_const_nhds :
      Tendsto (fun _t : ℝ => (x⁻¹)^2/2) atTop (𝓝 ((x⁻¹)^2/2))).sub hgap
    simpa only [sub_sub_cancel,sub_zero] using hs
  · have hz : x=0 := le_antisymm (le_of_not_gt hp) hx
    subst x
    simpa [positiveModeOffsetError,positiveSpectrumLog] using
      (tendsto_const_nhds : Tendsto (fun _t : ℝ => (0 : ℝ)) atTop (𝓝 0))

private theorem secondOffsetEqModes {m p n r : ℕ}
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

theorem actualCorrelatedMatrixLogDet_expected_positive_second_coefficient {m p n r : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (hr : r=(Matrix.fromRows B M).rank) (hR : 0<min m r)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=min m r)
    (hMoment : B.rank=0 ∨ r-B.rank=m ∨ (2 : ℝ)<((max m r-min m r+1 : ℕ) : ℝ)) :
    let R : ℝ := (min m r : ℕ)
    let S := fun z : ComplexSample (m := m) (n := p) =>
      ∑ j,positiveSpectrumLog (actualCorrelatedEigenvalue B M j z)
    let L := fun z : ComplexSample (m := m) (n := p) => ∑ j,(actualCorrelatedEigenvalue B M j z)⁻¹
    let Q := fun z : ComplexSample (m := m) (n := p) => ∑ j,((actualCorrelatedEigenvalue B M j z)⁻¹)^2
    Integrable Q (stdGaussian _) ∧
      Tendsto (fun t : ℝ => t*((∫ z,L z ∂stdGaussian _)-
        t*((∫ z,actualCorrelatedMatrixLogDet B M t z ∂stdGaussian _)-R*Real.log t-
          (∫ z,S z ∂stdGaussian _)))) atTop (𝓝 ((∫ z,Q z ∂stdGaussian _)/2)) := by
  classical
  intro R S L Q
  let μ := stdGaussian (ComplexSample (m := m) (n := p))
  let F := fun (t : ℝ) (z : ComplexSample (m := m) (n := p)) =>
    t*(L z-t*(actualCorrelatedMatrixLogDet B M t z-R*Real.log t-S z))
  have hMoment1 : B.rank=0 ∨ r-B.rank=m ∨ (1 : ℝ)<((max m r-min m r+1 : ℕ) : ℝ) := by
    rcases hMoment with hz|hz|hz
    · exact Or.inl hz
    · exact Or.inr (Or.inl hz)
    · exact Or.inr (Or.inr (by linarith))
  have hLI : Integrable L μ :=
    (actualCorrelatedMatrixLogDet_expected_positive_first_coefficient B M hr hR i hi hMoment1).1
  have hIq := (actual_singular_positive_inverse_realMoment_integrable_iff
    B M hr hR i hi (2 : ℝ) (by norm_num)).mpr hMoment
  have hI : Integrable (fun z => ((actualCorrelatedEigenvalue B M i z)⁻¹)^2) μ := by
    simpa only [Real.rpow_two] using hIq
  have hR' : 0<min m (Matrix.fromRows B M).rank := by rwa [← hr]
  obtain ⟨i0,hi0,hmi,hMin⟩ := exists_actualCorrelated_smallest_positive_coordinate B M hR'
  have he : i=i0 := Fin.ext (by rw [← hr] at hi0;omega)
  subst i0
  have hRank := actualCorrelatedRank_eq_generic_ae B M
  rw [← matrix_fromRows_rank_eq B M,← hr] at hRank
  have hS := integrable_actualCorrelated_positive_log_sum B M
  change Integrable S μ at hS
  have hQm : Measurable Q := by
    apply Finset.measurable_sum
    intro j _
    exact (measurable_actualCorrelatedEigenvalue B M j).inv.pow_const 2
  have hQnon (z : ComplexSample (m := m) (n := p)) : 0≤Q z :=
    Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hQb : ∀ᵐ z ∂μ,‖Q z‖≤(n : ℝ)*((actualCorrelatedEigenvalue B M i z)⁻¹)^2 := by
    filter_upwards [hMin] with z hz
    rw [Real.norm_eq_abs,abs_of_nonneg (hQnon z)]
    have hb (j : Fin (Fintype.card (Fin n))) :
        ((actualCorrelatedEigenvalue B M j z)⁻¹)^2≤((actualCorrelatedEigenvalue B M i z)⁻¹)^2 := by
      have hInv : (actualCorrelatedEigenvalue B M j z)⁻¹≤(actualCorrelatedEigenvalue B M i z)⁻¹ := by
        by_cases hp : 0<actualCorrelatedEigenvalue B M j z
        · simpa only [one_div] using one_div_le_one_div_of_le hz.1 (hz.2 j hp)
        · have hh : actualCorrelatedEigenvalue B M j z=0 := le_antisymm
            (le_of_not_gt hp) (actualCorrelatedEigenvalue_nonneg B M j z)
          rw [hh,_root_.inv_zero]
          exact inv_nonneg.mpr hz.1.le
      exact pow_le_pow_left₀ (inv_nonneg.mpr (actualCorrelatedEigenvalue_nonneg B M j z)) hInv 2
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hb j)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hh
  have hQI : Integrable Q μ := (hI.const_mul (n : ℝ)).mono' hQm.aestronglyMeasurable hQb
  have hFI (t : ℝ) (ht : 1≤t) : Integrable (F t) μ := by
    have hE := ((integrable_actualCorrelatedMatrixLogDet B M t (zero_le_one.trans ht)).sub
      (integrable_const (R*Real.log t))).sub hS
    exact (hLI.sub (hE.const_mul t)).const_mul t
  have hFb (t : ℝ) (ht : 1≤t) : ∀ᵐ z ∂μ,
      ‖F t z‖≤((n : ℝ)/2)*((actualCorrelatedEigenvalue B M i z)⁻¹)^2 := by
    have ht0 : 0<t := zero_lt_one.trans_le ht
    filter_upwards [hMin,hRank,hQb] with z hz hzr hQbz
    have hSum : (∑ j,t*((actualCorrelatedEigenvalue B M j z)⁻¹-
        t*positiveModeOffsetError (actualCorrelatedEigenvalue B M j z) t))=F t z := by
      rw [← Finset.mul_sum,Finset.sum_sub_distrib,← Finset.mul_sum,
        secondOffsetEqModes B M t ht0 z hzr]
    have hn : 0≤F t z := by
      rw [← hSum]
      exact Finset.sum_nonneg (fun j _ =>
        (modeSecondGapBound _ t (actualCorrelatedEigenvalue_nonneg B M j z) ht0).1)
    have hu : F t z≤Q z/2 := by
      rw [← hSum]
      have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
        (modeSecondGapBound _ t (actualCorrelatedEigenvalue_nonneg B M j z) ht0).2)
      simpa only [Q,Finset.sum_div] using hh
    rw [Real.norm_eq_abs,abs_of_nonneg hn]
    have hQle : Q z≤(n : ℝ)*((actualCorrelatedEigenvalue B M i z)⁻¹)^2 := by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (hQnon z)] using hQbz
    nlinarith
  have hConv : ∀ᵐ z ∂μ,Tendsto (fun t => F t z) atTop (𝓝 (Q z/2)) := by
    filter_upwards [hRank] with z hzr
    have hs := tendsto_finsetSum Finset.univ (fun j _ =>
      positiveModeOffsetError_second_scaled_tendsto (actualCorrelatedEigenvalue B M j z)
        (actualCorrelatedEigenvalue_nonneg B M j z))
    have hs' : Tendsto (fun t : ℝ => ∑ j,t*((actualCorrelatedEigenvalue B M j z)⁻¹-
        t*positiveModeOffsetError (actualCorrelatedEigenvalue B M j z) t)) atTop (𝓝 (Q z/2)) := by
      simpa only [Q,Finset.sum_div] using hs
    apply hs'.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    rw [← Finset.mul_sum,Finset.sum_sub_distrib,← Finset.mul_sum,
      secondOffsetEqModes B M t (zero_lt_one.trans_le ht) z hzr]
  have hD : Tendsto (fun t => ∫ z,F t z ∂μ) atTop (𝓝 (∫ z,Q z/2 ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun z => ((n : ℝ)/2)*((actualCorrelatedEigenvalue B M i z)⁻¹)^2)
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      exact (hFI t ht).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      exact hFb t ht
    · exact hI.const_mul _
    · exact hConv
  rw [integral_div] at hD
  refine ⟨hQI,?_⟩
  apply hD.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have hC : Integrable (actualCorrelatedMatrixLogDet B M t) μ :=
    integrable_actualCorrelatedMatrixLogDet B M t (zero_le_one.trans ht)
  have hE : Integrable (fun z => actualCorrelatedMatrixLogDet B M t z-R*Real.log t-S z) μ :=
    (hC.sub (integrable_const _)).sub hS
  dsimp only [F]
  rw [integral_const_mul,
    integral_sub (f := L) (g := fun z => t*(actualCorrelatedMatrixLogDet B M t z-R*Real.log t-S z))
      hLI (hE.const_mul t),integral_const_mul,
    integral_sub (f := fun z => actualCorrelatedMatrixLogDet B M t z-R*Real.log t)
      (g := S) (hC.sub (integrable_const _)) hS,
    integral_sub (f := actualCorrelatedMatrixLogDet B M t)
      (g := fun _ => R*Real.log t) hC (integrable_const _)]
  simp [μ]

end
end JinWishart
#print axioms JinWishart.positiveModeOffsetError_second_scaled_tendsto
#print axioms JinWishart.actualCorrelatedMatrixLogDet_expected_positive_second_coefficient
