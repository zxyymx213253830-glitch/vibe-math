import JinWishartFormalization.ActualCentralTwoByTwoMaximum

/-! Codex. Seed2026102409 exact triangular/lowerGamma determinant controls.
Closed actual maximum CDF and original T2, without assuming positivity of the formula.
[需人工审查] Original T2 mapping and weak-CDF interpretation. -/
open MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

theorem theorem2CentralTwoRow_XiDet_eq_closedCDF (x : ℝ) (hx : 0≤x) :
    (theorem2XiMatrix 2 2 0 (by omega) (by omega) (fun j : Fin 0 => Fin.elim0 j) x).det=
      ((1-(x^2+2)*Real.exp (-x)+Real.exp (-2*x) : ℝ) : ℂ) := by
  have h := eq_sub_of_add_eq (theorem2XiMatrix_add_theorem1PsiMatrix
    2 2 0 (by omega) (by omega) (fun j : Fin 0 => Fin.elim0 j) x)
  rw [theorem1CentralTwoRow_PsiMatrix x hx,theorem1CentralTwoRow_PsiMatrix 0 (by norm_num)] at h
  norm_num at h
  rw [h,Matrix.det_fin_two]
  change (2-(Real.exp (-x) : ℂ)*((x : ℂ)^2+2*(x : ℂ)+2))*
      (1-(Real.exp (-x) : ℂ))-
      (1-(Real.exp (-x) : ℂ)*((x : ℂ)+1))*
      (1-(Real.exp (-x) : ℂ)*((x : ℂ)+1))=_
  have he : Real.exp (-2*x)=Real.exp (-x)^2 := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  rw [he]
  norm_num only [Real.exp_zero,Complex.ofReal_one]
  push_cast
  ring

theorem actualCentralTwoByTwo_maximum_CDF (x : ℝ) (hx : 0≤x) :
    ((stdGaussian (ComplexSample (m := 2) (n := 2)))
      {z | (centralTwoByTwoEigenpair z).1≤x}).toReal=
        1-(x^2+2)*Real.exp (-x)+Real.exp (-2*x) := by
  have hd0 := (ordered_square_gap_moment_identity (exponentialIntervalMeasure x)
    (by simpa using exponentialInterval_integrable_pow x 1) (exponentialInterval_integrable_pow x 2)).1
  have hd : twoMomentDeterminant (exponentialIntervalMeasure x)=
      1-(x^2+2)*Real.exp (-x)+Real.exp (-2*x) :=
    Complex.ofReal_injective ((theorem2CentralTwoRow_XiDet_eq_intervalMoments x hx).symm.trans
      (theorem2CentralTwoRow_XiDet_eq_closedCDF x hx))
  rw [actualCentralTwoByTwo_maximumCDF_eq_momentDet,ENNReal.toReal_ofReal hd0,hd]

theorem theorem2CentralTwoRow_candidate_eq_closedCDF (x : ℝ) (hx : 0≤x) :
    theorem2CdfCandidate 2 2 0 (by omega) (by omega) (fun j : Fin 0 => Fin.elim0 j) x=
      1-(x^2+2)*Real.exp (-x)+Real.exp (-2*x) := by
  rw [theorem2CentralTwoRow_candidate_eq_actualCDF x hx,actualCentralTwoByTwo_maximum_CDF x hx]

end
end JinWishart
#print axioms JinWishart.theorem2CentralTwoRow_XiDet_eq_closedCDF
#print axioms JinWishart.actualCentralTwoByTwo_maximum_CDF
#print axioms JinWishart.theorem2CentralTwoRow_candidate_eq_closedCDF
