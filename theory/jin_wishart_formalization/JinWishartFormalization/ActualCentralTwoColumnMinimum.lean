import JinWishartFormalization.PowerExponentialTailMoments
import JinWishartFormalization.ActualCentralTwoColumnMaximum
import JinWishartFormalization.CentralTwoColumnJointDensity

/-! Codex. Actual all-row two-column minimum and unchanged original T1.
Seed2026102416 precedes source. [需人工审查] Ordered support and restricted integrals. -/
open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal
namespace JinWishart
noncomputable section

private theorem powerTail_prod_density (d : ℕ) (x : ℝ) (hx : 0≤x) :
    (powerExponentialTailMeasure d x).prod (powerExponentialTailMeasure d x)=
      ((volume : Measure (ℝ × ℝ)).restrict ((Ioi x) ×ˢ (Ioi x))).withDensity
        (fun z => ENNReal.ofReal (|z.1*z.2|^d*Real.exp (-(z.1+z.2)))) := by
  unfold powerExponentialTailMeasure
  rw [max_eq_right hx,prod_withDensity (by fun_prop) (by fun_prop),Measure.prod_restrict,← Measure.volume_eq_prod]
  congr 1
  funext z
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  calc
    _ = |z.1*z.2|^d*(Real.exp (-z.1)*Real.exp (-z.2)) := by rw [abs_mul,mul_pow];ring
    _ = _ := by rw [← Real.exp_add];congr 1;ring

private theorem min_weighted_ordered_integral (d : ℕ) (x : ℝ) (hx : 0≤x) :
    ENNReal.ofReal ((d.factorial : ℝ)*((d+1).factorial : ℝ))*
      (centralTwoColumnJointEigenvalueLaw d) {y | x<y.2}=
    ∫⁻ z in {z : ℝ × ℝ | z.2<z.1},ENNReal.ofReal ((z.1-z.2)^2)
      ∂(powerExponentialTailMeasure d x).prod (powerExponentialTailMeasure d x) := by
  let P : Set (ℝ × ℝ) := {z | x<z.2}
  let S : Set (ℝ × ℝ) := {z | 0<z.2 ∧ z.2<z.1}
  let O : Set (ℝ × ℝ) := {z | z.2<z.1}
  let R : Set (ℝ × ℝ) := (Ioi x) ×ˢ (Ioi x)
  let C : ℝ := (d.factorial : ℝ)*((d+1).factorial : ℝ)
  let W : ℝ × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (|z.1*z.2|^d*Real.exp (-(z.1+z.2)))
  let G : ℝ × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal ((z.1-z.2)^2)
  have hP : MeasurableSet P := measurableSet_lt measurable_const measurable_snd
  have hO : MeasurableSet O := measurableSet_lt measurable_snd measurable_fst
  have hR : MeasurableSet R := measurableSet_Ioi.prod measurableSet_Ioi
  have hW : Measurable W := by dsimp [W];fun_prop
  have hG : Measurable G := by dsimp [G];fun_prop
  have hC : 0<C := by dsimp [C];positivity
  have hsets : P ∩ S=R ∩ O := by
    ext ⟨u,v⟩
    simp only [P,S,R,O,mem_inter_iff,mem_prod,mem_Ioi,mem_setOf_eq]
    constructor
    · rintro ⟨hvx,hv0,hvu⟩
      exact ⟨⟨lt_trans hvx hvu,hvx⟩,hvu⟩
    · rintro ⟨⟨hux,hvx⟩,hvu⟩
      exact ⟨hvx,lt_of_le_of_lt hx hvx,hvu⟩
  have hpaper : (fun z => ENNReal.ofReal C*centralTwoColumnEigenvalueDensity d z)=
      S.indicator (fun z => W z*G z) := by
    funext z
    by_cases hz : 0<z.2 ∧ z.2<z.1
    · have hz0 : 0≤z.1*z.2 := mul_nonneg (le_trans hz.1.le hz.2.le) hz.1.le
      simp only [centralTwoColumnEigenvalueDensity,if_pos hz,
        Set.indicator_of_mem (show z ∈ S from hz)]
      dsimp [W,G]
      rw [← ENNReal.ofReal_mul hC.le,← ENNReal.ofReal_mul (by positivity),abs_of_nonneg hz0]
      congr 1
      dsimp [C]
      field_simp
    · simp [centralTwoColumnEigenvalueDensity,S,hz]
  have hright : (∫⁻ z in O,G z ∂(powerExponentialTailMeasure d x).prod (powerExponentialTailMeasure d x))=
      ∫⁻ z : ℝ × ℝ,(R ∩ O).indicator (fun z => W z*G z) z := by
    rw [← lintegral_indicator hO,powerTail_prod_density d x hx,
      lintegral_withDensity_eq_lintegral_mul _ hW (hG.indicator hO),← lintegral_indicator hR]
    apply lintegral_congr
    intro z
    by_cases hzR : z ∈ R <;> by_cases hzO : z ∈ O <;> simp [hzR,hzO,Set.mem_inter_iff]
  change ENNReal.ofReal C*(centralTwoColumnJointEigenvalueLaw d) P=_
  rw [actualCentralTwoColumn_jointEigenvalueDensity,withDensity_apply _ hP,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,← lintegral_indicator hP]
  calc
    _ = ∫⁻ z : ℝ × ℝ,(R ∩ O).indicator (fun z => W z*G z) z := by
      rw [hpaper,Set.indicator_indicator,hsets]
    _ = _ := hright.symm

theorem actualCentralTwoColumn_minimum_tail_momentDet (d : ℕ) (x : ℝ) (hx : 0≤x) :
    ((stdGaussian (ComplexSample (m := d+2) (n := 2)))
      {z | x<(centralTwoColumnEigenpair z).2}).toReal=
      twoMomentDeterminant (powerExponentialTailMeasure d x)/
        ((d.factorial : ℝ)*((d+1).factorial : ℝ)) := by
  have hg := ordered_square_gap_moment_identity (powerExponentialTailMeasure d x)
    (by simpa using powerExponentialTail_integrable_pow d x 1)
    (powerExponentialTail_integrable_pow d x 2)
  have h := min_weighted_ordered_integral d x hx
  rw [hg.2] at h
  have hr := congrArg ENNReal.toReal h
  have hC : 0<(d.factorial : ℝ)*((d+1).factorial : ℝ) := by positivity
  have hpairM : Measurable (centralTwoColumnEigenpair (m := d+2)) :=
    measurable_twoColumnMatrixEigenpair.comp measurable_complexSampleGram
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal hC.le,ENNReal.toReal_ofReal hg.1,
    centralTwoColumnJointEigenvalueLaw,Measure.map_apply
      hpairM
      (measurableSet_lt measurable_const measurable_snd)] at hr
  exact (eq_div_iff hC.ne').mpr (by simpa [mul_comm] using hr)


theorem theorem1CentralTwoColumn_candidate_eq_actualCDF (d : ℕ) (x : ℝ) (hx : 0≤x) :
    theorem1CdfCandidate 2 (d+2) 0 (by omega) (by omega) (fun j : Fin 0 => Fin.elim0 j) x=
      ((stdGaussian (ComplexSample (m := d+2) (n := 2)))
        {z | (centralTwoColumnEigenpair z).2≤x}).toReal := by
  have hg := (ordered_square_gap_moment_identity (powerExponentialTailMeasure d x)
    (by simpa using powerExponentialTail_integrable_pow d x 1)
    (powerExponentialTail_integrable_pow d x 2)).1
  have hC : 0≤(d.factorial : ℝ)*((d+1).factorial : ℝ) := by positivity
  have hpairM : Measurable (centralTwoColumnEigenpair (m := d+2)) :=
    measurable_twoColumnMatrixEigenpair.comp measurable_complexSampleGram
  have hS : MeasurableSet {z : ComplexSample (m := d+2) (n := 2) | (centralTwoColumnEigenpair z).2≤x} :=
    measurableSet_le (measurable_snd.comp hpairM) measurable_const
  have h := probReal_add_probReal_compl
    (μ := stdGaussian (ComplexSample (m := d+2) (n := 2))) hS
  have he : {z : ComplexSample (m := d+2) (n := 2) | (centralTwoColumnEigenpair z).2≤x}ᶜ=
      {z | x<(centralTwoColumnEigenpair z).2} := by ext z;simp
  simp only [Measure.real,he] at h
  rw [actualCentralTwoColumn_minimum_tail_momentDet d x hx] at h
  rw [theorem1CdfCandidate,theorem1CentralTwoColumn_PsiDet_eq_tailMoments d x hx,
    theorem1CentralTwoColumn_PsiDet_zero,Complex.norm_of_nonneg hg,Complex.norm_of_nonneg hC]
  linarith
end
end JinWishart
#print axioms JinWishart.actualCentralTwoColumn_minimum_tail_momentDet
#print axioms JinWishart.theorem1CentralTwoColumn_candidate_eq_actualCDF
