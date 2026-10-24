import JinWishartFormalization.PowerExponentialIntervalMoments
import JinWishartFormalization.CentralTwoColumnJointDensity

/-! Codex. Actual all-row two-column maximum and unchanged original T2.
Seed2026102415 precedes source. [需人工审查] Ordered support and restricted integrals. -/
open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal
namespace JinWishart
noncomputable section

private theorem powerInterval_prod_density (d : ℕ) (x : ℝ) :
    (powerExponentialIntervalMeasure d x).prod (powerExponentialIntervalMeasure d x)=
      ((volume : Measure (ℝ × ℝ)).restrict ((Ioc 0 x) ×ˢ (Ioc 0 x))).withDensity
        (fun z => ENNReal.ofReal (|z.1*z.2|^d*Real.exp (-(z.1+z.2)))) := by
  unfold powerExponentialIntervalMeasure
  rw [prod_withDensity (by fun_prop) (by fun_prop),Measure.prod_restrict,← Measure.volume_eq_prod]
  congr 1
  funext z
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  calc
    _ = |z.1*z.2|^d*(Real.exp (-z.1)*Real.exp (-z.2)) := by rw [abs_mul,mul_pow];ring
    _ = _ := by rw [← Real.exp_add];congr 1;ring

private theorem max_weighted_ordered_integral (d : ℕ) (x : ℝ) :
    ENNReal.ofReal ((d.factorial : ℝ)*((d+1).factorial : ℝ))*
      (centralTwoColumnJointEigenvalueLaw d) {y | y.1≤x}=
    ∫⁻ z in {z : ℝ × ℝ | z.2<z.1},ENNReal.ofReal ((z.1-z.2)^2)
      ∂(powerExponentialIntervalMeasure d x).prod (powerExponentialIntervalMeasure d x) := by
  let P : Set (ℝ × ℝ) := {z | z.1≤x}
  let S : Set (ℝ × ℝ) := {z | 0<z.2 ∧ z.2<z.1}
  let O : Set (ℝ × ℝ) := {z | z.2<z.1}
  let R : Set (ℝ × ℝ) := (Ioc 0 x) ×ˢ (Ioc 0 x)
  let C : ℝ := (d.factorial : ℝ)*((d+1).factorial : ℝ)
  let W : ℝ × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (|z.1*z.2|^d*Real.exp (-(z.1+z.2)))
  let G : ℝ × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal ((z.1-z.2)^2)
  have hP : MeasurableSet P := measurableSet_le measurable_fst measurable_const
  have hO : MeasurableSet O := measurableSet_lt measurable_snd measurable_fst
  have hR : MeasurableSet R := measurableSet_Ioc.prod measurableSet_Ioc
  have hW : Measurable W := by dsimp [W];fun_prop
  have hG : Measurable G := by dsimp [G];fun_prop
  have hC : 0<C := by dsimp [C];positivity
  have hsets : P ∩ S=R ∩ O := by
    ext ⟨u,v⟩
    simp only [P,S,R,O,mem_inter_iff,mem_prod,mem_Ioc,mem_setOf_eq]
    constructor
    · rintro ⟨hux,hv0,hvu⟩
      exact ⟨⟨⟨lt_trans hv0 hvu,hux⟩,⟨hv0,le_trans hvu.le hux⟩⟩,hvu⟩
    · rintro ⟨⟨⟨hu0,hux⟩,⟨hv0,hvx⟩⟩,hvu⟩
      exact ⟨hux,hv0,hvu⟩
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
  have hright : (∫⁻ z in O,G z ∂(powerExponentialIntervalMeasure d x).prod (powerExponentialIntervalMeasure d x))=
      ∫⁻ z : ℝ × ℝ,(R ∩ O).indicator (fun z => W z*G z) z := by
    rw [← lintegral_indicator hO,powerInterval_prod_density,
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

theorem actualCentralTwoColumn_maximum_momentDet (d : ℕ) (x : ℝ) :
    ((stdGaussian (ComplexSample (m := d+2) (n := 2)))
      {z | (centralTwoColumnEigenpair z).1≤x}).toReal=
      twoMomentDeterminant (powerExponentialIntervalMeasure d x)/
        ((d.factorial : ℝ)*((d+1).factorial : ℝ)) := by
  have hg := ordered_square_gap_moment_identity (powerExponentialIntervalMeasure d x)
    (by simpa using powerExponentialInterval_integrable_pow d x 1)
    (powerExponentialInterval_integrable_pow d x 2)
  have h := max_weighted_ordered_integral d x
  rw [hg.2] at h
  have hr := congrArg ENNReal.toReal h
  have hC : 0<(d.factorial : ℝ)*((d+1).factorial : ℝ) := by positivity
  have hpairM : Measurable (centralTwoColumnEigenpair (m := d+2)) :=
    measurable_twoColumnMatrixEigenpair.comp measurable_complexSampleGram
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal hC.le,ENNReal.toReal_ofReal hg.1,
    centralTwoColumnJointEigenvalueLaw,Measure.map_apply
      hpairM
      (measurableSet_le measurable_fst measurable_const)] at hr
  exact (eq_div_iff hC.ne').mpr (by simpa [mul_comm] using hr)

theorem theorem1CentralTwoColumn_PsiDet_zero (d : ℕ) :
    (theorem1PsiMatrix 2 (d+2) 0 (by omega) (by omega) (fun j : Fin 0 => Fin.elim0 j) 0).det=
      (((d.factorial : ℝ)*((d+1).factorial : ℝ) : ℝ) : ℂ) := by
  have hm : theorem1PsiMatrix 2 (d+2) 0 (by omega) (by omega) (fun j : Fin 0 => Fin.elim0 j) 0=
      (!![((d+2).factorial : ℂ),((d+1).factorial : ℂ);((d+1).factorial : ℂ),(d.factorial : ℂ)] : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [theorem1PsiMatrix,theorem1PsiEntry,theorem1GammaIndex,upperGammaNat_at_zero_eq_factorial]
  rw [hm,Matrix.det_fin_two]
  change ((d+2).factorial : ℂ)*(d.factorial : ℂ)-((d+1).factorial : ℂ)*((d+1).factorial : ℂ)=_
  simp only [show d+2=(d+1)+1 by omega,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  push_cast
  ring

theorem theorem2CentralTwoColumn_candidate_eq_actualCDF (d : ℕ) (x : ℝ) (hx : 0≤x) :
    theorem2CdfCandidate 2 (d+2) 0 (by omega) (by omega) (fun j : Fin 0 => Fin.elim0 j) x=
      ((stdGaussian (ComplexSample (m := d+2) (n := 2)))
        {z | (centralTwoColumnEigenpair z).1≤x}).toReal := by
  have hg := (ordered_square_gap_moment_identity (powerExponentialIntervalMeasure d x)
    (by simpa using powerExponentialInterval_integrable_pow d x 1)
    (powerExponentialInterval_integrable_pow d x 2)).1
  have hC : 0≤(d.factorial : ℝ)*((d+1).factorial : ℝ) := by positivity
  rw [theorem2CdfCandidate,theorem2CentralTwoColumn_XiDet_eq_intervalMoments d x hx,
    theorem1CentralTwoColumn_PsiDet_zero,Complex.norm_of_nonneg hg,Complex.norm_of_nonneg hC,
    actualCentralTwoColumn_maximum_momentDet]
end
end JinWishart
#print axioms JinWishart.actualCentralTwoColumn_maximum_momentDet
#print axioms JinWishart.theorem1CentralTwoColumn_PsiDet_zero
#print axioms JinWishart.theorem2CentralTwoColumn_candidate_eq_actualCDF
