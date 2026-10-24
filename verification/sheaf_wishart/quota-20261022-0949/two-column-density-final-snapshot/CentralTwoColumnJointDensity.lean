import JinWishartFormalization.TwoColumnOrderedSpectralMap
import JinWishartFormalization.ActualCentralTwoByTwoJointDensity

/-! Codex. Actual central two-column joint density for every row surplus.
Seed2026102414 controls before source. Reuses square2 joint density and
actual determinant-power bias; no new angular change of variables.
[需人工审查] Weighted pushforward, normalization and actual ordered model. -/
open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal ComplexOrder
namespace JinWishart
noncomputable section

def centralTwoColumnJointEigenvalueLaw (d : ℕ) : Measure (ℝ × ℝ) :=
  (stdGaussian (ComplexSample (m := d+2) (n := 2))).map centralTwoColumnEigenpair

def centralTwoColumnEigenvalueDensity (d : ℕ) (y : ℝ × ℝ) : ℝ≥0∞ :=
  if 0<y.2 ∧ y.2<y.1 then
    ENNReal.ofReal (Real.exp (-(y.1+y.2))*(y.1-y.2)^2*(y.1*y.2)^d/
      ((d.factorial : ℝ)*((d+1).factorial : ℝ))) else 0

private theorem base_pair_eq : (centralTwoColumnEigenpair (m := 2))=centralTwoByTwoEigenpair := by
  funext z
  simpa [centralTwoByTwoEigenpair] using centralTwoColumnEigenpair_eq_ordered z

private theorem meas_pair (m : ℕ) : Measurable (centralTwoColumnEigenpair (m := m)) :=
  measurable_twoColumnMatrixEigenpair.comp measurable_complexSampleGram

private theorem bias_constant (d : ℕ) : centralDeterminantPowerMoment 0 2 d=
    (d.factorial : ℝ)*((d+1).factorial : ℝ) := by
  simp [centralDeterminantPowerMoment,Fin.prod_univ_two,Nat.add_comm]

theorem centralTwoColumn_joint_spectral_bias (d : ℕ) :
    centralTwoByTwoJointEigenvalueLaw.withDensity (fun y => ENNReal.ofReal ((y.1*y.2)^d))=
      ENNReal.ofReal ((d.factorial : ℝ)*((d+1).factorial : ℝ)) •
        centralTwoColumnJointEigenvalueLaw d := by
  have hw : Measurable (fun y : ℝ × ℝ => ENNReal.ofReal ((y.1*y.2)^d)) := by fun_prop
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_withDensity_eq_lintegral_mul _ hw hF,centralTwoByTwoJointEigenvalueLaw,
    lintegral_map (hw.mul hF) measurable_centralTwoByTwoEigenpair,
    lintegral_smul_measure,centralTwoColumnJointEigenvalueLaw,lintegral_map hF (meas_pair (d+2))]
  have h := lintegral_complexWishart_determinant_power_bias 0 2 d
    (fun A => F (twoColumnMatrixEigenpair A)) (hF.comp measurable_twoColumnMatrixEigenpair)
  simp only [Nat.zero_add] at h
  have hW : Measurable (fun A : Matrix (Fin 2) (Fin 2) ℂ =>
      ENNReal.ofReal (‖A.det‖^d)*F (twoColumnMatrixEigenpair A)) :=
    (by fun_prop : Measurable (fun A : Matrix (Fin 2) (Fin 2) ℂ => ENNReal.ofReal (‖A.det‖^d))).mul
      (hF.comp measurable_twoColumnMatrixEigenpair)
  have hFM : Measurable (fun A : Matrix (Fin 2) (Fin 2) ℂ => F (twoColumnMatrixEigenpair A)) :=
    hF.comp measurable_twoColumnMatrixEigenpair
  simp only [complexWishart] at h
  rw [lintegral_map hW measurable_complexSampleGram,
    lintegral_map hFM measurable_complexSampleGram,
    bias_constant] at h
  change _ = ENNReal.ofReal ((d.factorial : ℝ)*((d+1).factorial : ℝ))*
    ∫⁻ z,F (centralTwoColumnEigenpair z) ∂stdGaussian (ComplexSample (m := d+2) (n := 2))
  change (∫⁻ z,ENNReal.ofReal (‖(complexSampleGram z).det‖^d)*F (centralTwoColumnEigenpair z)
    ∂stdGaussian (ComplexSample (m := 2) (n := 2)))=
    ENNReal.ofReal ((d.factorial : ℝ)*((d+1).factorial : ℝ))*
      ∫⁻ z,F (centralTwoColumnEigenpair z) ∂stdGaussian (ComplexSample (m := d+2) (n := 2)) at h
  rw [← h]
  apply lintegral_congr
  intro z
  have hp : ‖(complexSampleGram z).det‖=(centralTwoColumnEigenpair z).1*(centralTwoColumnEigenpair z).2 :=
    twoColumnMatrixEigenpair_det_product _ (complexGram_posSemidef (complexSampleMatrix z))
  rw [hp,base_pair_eq]
  rfl

theorem actualCentralTwoColumn_jointEigenvalueDensity (d : ℕ) :
    centralTwoColumnJointEigenvalueLaw d=
      (volume : Measure (ℝ × ℝ)).withDensity (centralTwoColumnEigenvalueDensity d) := by
  let C : ℝ := (d.factorial : ℝ)*((d+1).factorial : ℝ)
  have hC : 0<C := by dsimp [C];positivity
  have hp : Measurable centralTwoByTwoPaperEigenvalueDensity := by
    unfold centralTwoByTwoPaperEigenvalueDensity
    exact Measurable.ite (by measurability) (by fun_prop) measurable_const
  have hw : Measurable (fun y : ℝ × ℝ => ENNReal.ofReal ((y.1*y.2)^d)) := by fun_prop
  have h := centralTwoColumn_joint_spectral_bias d
  rw [actualCentralTwoByTwo_jointEigenvalueDensity,← withDensity_mul _ hp hw] at h
  have hd : (fun y => centralTwoByTwoPaperEigenvalueDensity y*ENNReal.ofReal ((y.1*y.2)^d))=
      fun y => ENNReal.ofReal C*centralTwoColumnEigenvalueDensity d y := by
    funext y
    by_cases hy : 0<y.2 ∧ y.2<y.1
    · rw [centralTwoByTwoPaperEigenvalueDensity,if_pos hy,centralTwoColumnEigenvalueDensity,if_pos hy]
      rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul hC.le]
      congr 1
      dsimp [C]
      field_simp
    · simp [centralTwoByTwoPaperEigenvalueDensity,centralTwoColumnEigenvalueDensity,hy]
  change (volume : Measure (ℝ × ℝ)).withDensity
    (fun y => centralTwoByTwoPaperEigenvalueDensity y*ENNReal.ofReal ((y.1*y.2)^d))=_ at h
  rw [hd] at h
  change (volume : Measure (ℝ × ℝ)).withDensity
    (ENNReal.ofReal C • centralTwoColumnEigenvalueDensity d)=_ at h
  rw [withDensity_smul' _ _ ENNReal.ofReal_ne_top] at h
  change ENNReal.ofReal C • (volume : Measure (ℝ × ℝ)).withDensity (centralTwoColumnEigenvalueDensity d)=
    ENNReal.ofReal C • centralTwoColumnJointEigenvalueLaw d at h
  have hi : (ENNReal.ofReal C)⁻¹*ENNReal.ofReal C=1 :=
    ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hC)) ENNReal.ofReal_ne_top
  have hh := congrArg (fun ν : Measure (ℝ × ℝ) => (ENNReal.ofReal C)⁻¹ • ν) h
  simpa only [smul_smul,hi,one_smul] using hh.symm
end
end JinWishart
#print axioms JinWishart.centralTwoColumn_joint_spectral_bias
#print axioms JinWishart.actualCentralTwoColumn_jointEigenvalueDensity
