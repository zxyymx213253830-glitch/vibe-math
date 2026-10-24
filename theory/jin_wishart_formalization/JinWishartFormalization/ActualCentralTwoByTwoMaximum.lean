import JinWishartFormalization.ExponentialIntervalMoments
import JinWishartFormalization.ActualCentralTwoByTwoJointDensity

/-! Codex. Seed2026102409 exact max-CDF/moment and normalization controls.
Actual maximum event and ORIGINAL central2x2 T2 candidate, no density premise.
[需人工审查] Restricted product measure, strict/weak events and original T2 mapping. -/
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace JinWishart
noncomputable section

private theorem exponentialInterval_prod_density (x : ℝ) :
    (exponentialIntervalMeasure x).prod (exponentialIntervalMeasure x)=
      ((volume : Measure (ℝ × ℝ)).restrict ((Ioc 0 x) ×ˢ (Ioc 0 x))).withDensity
        (fun z => ENNReal.ofReal (Real.exp (-(z.1+z.2)))) := by
  unfold exponentialIntervalMeasure
  rw [prod_withDensity (by fun_prop) (by fun_prop),Measure.prod_restrict,← Measure.volume_eq_prod]
  congr 1
  funext z
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _),← Real.exp_add]
  congr 1
  ring

private theorem actualMaximum_eq_orderedGapIntegral (x : ℝ) :
    (stdGaussian (ComplexSample (m := 2) (n := 2))) {z | (centralTwoByTwoEigenpair z).1≤x}=
      ∫⁻ z in {z : ℝ × ℝ | z.2<z.1}, ENNReal.ofReal ((z.1-z.2)^2)
        ∂(exponentialIntervalMeasure x).prod (exponentialIntervalMeasure x) := by
  let P : Set (ℝ × ℝ) := {z | z.1≤x}
  let S : Set (ℝ × ℝ) := {z | 0<z.2 ∧ z.2<z.1}
  let O : Set (ℝ × ℝ) := {z | z.2<z.1}
  let R : Set (ℝ × ℝ) := (Ioc 0 x) ×ˢ (Ioc 0 x)
  let W : ℝ × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.exp (-(z.1+z.2)))
  let G : ℝ × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal ((z.1-z.2)^2)
  have hP : MeasurableSet P := measurableSet_le measurable_fst measurable_const
  have hS : MeasurableSet S := by dsimp [S];measurability
  have hO : MeasurableSet O := measurableSet_lt measurable_snd measurable_fst
  have hR : MeasurableSet R := measurableSet_Ioc.prod measurableSet_Ioc
  have hW : Measurable W := by dsimp [W];fun_prop
  have hG : Measurable G := by dsimp [G];fun_prop
  have hsets : P ∩ S=R ∩ O := by
    ext ⟨u,v⟩
    simp only [P,S,R,O,mem_inter_iff,mem_prod,mem_Ioc,mem_setOf_eq]
    constructor
    · rintro ⟨hux,hv0,hvu⟩
      exact ⟨⟨⟨lt_trans hv0 hvu,hux⟩,⟨hv0,le_trans hvu.le hux⟩⟩,hvu⟩
    · rintro ⟨⟨⟨hu0,hux⟩,⟨hv0,hvx⟩⟩,hvu⟩
      exact ⟨hux,hv0,hvu⟩
  have hpaper : centralTwoByTwoPaperEigenvalueDensity=S.indicator (fun z => W z*G z) := by
    funext z
    by_cases hz : 0<z.2 ∧ z.2<z.1
    · simp [centralTwoByTwoPaperEigenvalueDensity,S,W,G,hz,ENNReal.ofReal_mul (Real.exp_nonneg _)]
    · simp [centralTwoByTwoPaperEigenvalueDensity,S,hz]
  have hright : (∫⁻ z in O,G z ∂(exponentialIntervalMeasure x).prod (exponentialIntervalMeasure x))=
      ∫⁻ z : ℝ × ℝ,(R ∩ O).indicator (fun z => W z*G z) z := by
    rw [← lintegral_indicator hO,exponentialInterval_prod_density,
      lintegral_withDensity_eq_lintegral_mul _ hW (hG.indicator hO),← lintegral_indicator hR]
    apply lintegral_congr
    intro z
    by_cases hzR : z ∈ R <;> by_cases hzO : z ∈ O <;>
      simp [hzR,hzO,Set.mem_inter_iff]
  calc
    _ = centralTwoByTwoJointEigenvalueLaw P := by
      rw [centralTwoByTwoJointEigenvalueLaw,Measure.map_apply measurable_centralTwoByTwoEigenpair hP]
      rfl
    _ = ∫⁻ z in P,centralTwoByTwoPaperEigenvalueDensity z := by
      rw [actualCentralTwoByTwo_jointEigenvalueDensity,withDensity_apply _ hP]
    _ = ∫⁻ z : ℝ × ℝ,(R ∩ O).indicator (fun z => W z*G z) z := by
      rw [← lintegral_indicator hP,hpaper,Set.indicator_indicator,hsets]
    _ = _ := hright.symm

theorem actualCentralTwoByTwo_maximumCDF_eq_momentDet (x : ℝ) :
    (stdGaussian (ComplexSample (m := 2) (n := 2))) {z | (centralTwoByTwoEigenpair z).1≤x}=
      ENNReal.ofReal (twoMomentDeterminant (exponentialIntervalMeasure x)) := by
  rw [actualMaximum_eq_orderedGapIntegral]
  exact (ordered_square_gap_moment_identity (exponentialIntervalMeasure x)
    (by simpa using exponentialInterval_integrable_pow x 1) (exponentialInterval_integrable_pow x 2)).2

theorem theorem2CentralTwoRow_candidate_eq_actualCDF (x : ℝ) (hx : 0≤x) :
    theorem2CdfCandidate 2 2 0 (by omega) (by omega) (fun j : Fin 0 => Fin.elim0 j) x=
      ((stdGaussian (ComplexSample (m := 2) (n := 2)))
        {z | (centralTwoByTwoEigenpair z).1≤x}).toReal := by
  have hd := (ordered_square_gap_moment_identity (exponentialIntervalMeasure x)
    (by simpa using exponentialInterval_integrable_pow x 1) (exponentialInterval_integrable_pow x 2)).1
  rw [theorem2CdfCandidate,theorem1CentralTwoRow_PsiDet_norm_zero,div_one,
    theorem2CentralTwoRow_XiDet_eq_intervalMoments x hx,Complex.norm_of_nonneg hd,
    actualCentralTwoByTwo_maximumCDF_eq_momentDet,ENNReal.toReal_ofReal hd]

end
end JinWishart
#print axioms JinWishart.actualCentralTwoByTwo_maximumCDF_eq_momentDet
#print axioms JinWishart.theorem2CentralTwoRow_candidate_eq_actualCDF
