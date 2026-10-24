import JinWishartFormalization.TwoRowActualNormalizedDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! Codex. Seed2026102405 controls before source.
Trace/traceless coordinates and exact volume factor for central 2x2 G2.
[需人工审查] Lebesgue coordinate convention; joint eigenvalue law still separate. -/
open MeasureTheory Set
open scoped ENNReal
namespace JinWishart
noncomputable section

def twoRowTraceCoordinates (q : GramChartSpace) : GramChartSpace :=
  ![(q 0+q 3)/2,(q 0-q 3)/2,q 1,q 2]

def twoRowTraceInverse (p : GramChartSpace) : GramChartSpace :=
  ![p 0+p 1,p 2,p 3,p 0-p 1]

def twoRowTraceEquiv : GramChartSpace ≃ₗ[ℝ] GramChartSpace where
  toFun := twoRowTraceCoordinates
  invFun := twoRowTraceInverse
  left_inv q := by ext i;fin_cases i <;> simp [twoRowTraceCoordinates,twoRowTraceInverse] <;> ring
  right_inv p := by ext i;fin_cases i <;> simp [twoRowTraceCoordinates,twoRowTraceInverse] <;> ring
  map_add' q p := by ext i;fin_cases i <;> simp [twoRowTraceCoordinates] <;> ring
  map_smul' r q := by ext i;fin_cases i <;> simp [twoRowTraceCoordinates] <;> ring

theorem twoRowTraceEquiv_det : twoRowTraceEquiv.toLinearMap.det=-(1/2 : ℝ) := by
  rw [← LinearMap.det_toMatrix']
  have hm : LinearMap.toMatrix' twoRowTraceEquiv.toLinearMap=
      (!![(1/2 : ℝ),0,0,1/2;1/2,0,0,-1/2;0,1,0,0;0,0,1,0] : Matrix (Fin 4) (Fin 4) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [LinearMap.toMatrix'_apply,twoRowTraceEquiv,twoRowTraceCoordinates,Pi.single_apply]
  rw [hm,Matrix.det_succ_row_zero]
  norm_num [Fin.sum_univ_succ,Matrix.submatrix_apply,Matrix.det_fin_three,Fin.succAbove]

theorem map_volume_twoRowTraceEquiv :
    (volume : Measure GramChartSpace).map twoRowTraceEquiv=(2 : ℝ≥0∞) • volume := by
  have h := map_linearMap_addHaar_eq_smul_addHaar (volume : Measure GramChartSpace)
    (f := twoRowTraceEquiv.toLinearMap) (by rw [twoRowTraceEquiv_det];norm_num)
  simpa [twoRowTraceEquiv_det] using h

theorem twoRowTraceCoordinates_cone (q : GramChartSpace) :
    (0<q 0 ∧ q 1^2+q 2^2<q 0*q 3) ↔
    (0<twoRowTraceCoordinates q 0 ∧
      (twoRowTraceCoordinates q 1)^2+(twoRowTraceCoordinates q 2)^2+
        (twoRowTraceCoordinates q 3)^2<(twoRowTraceCoordinates q 0)^2) := by
  change (0<q 0 ∧ q 1^2+q 2^2<q 0*q 3) ↔
    (0<(q 0+q 3)/2 ∧ ((q 0-q 3)/2)^2+q 1^2+q 2^2<((q 0+q 3)/2)^2)
  constructor
  · rintro ⟨ha,hd⟩
    have hdpos : 0<q 3 := by
      have hprod : 0<q 0*q 3 := lt_of_le_of_lt (by positivity) hd
      exact (mul_pos_iff_of_pos_left ha).mp hprod
    constructor <;> nlinarith
  · rintro ⟨ht,hr⟩
    constructor <;> nlinarith [sq_nonneg (q 1),sq_nonneg (q 2)]

theorem twoRowTraceCone_iff_norm (p : GramChartSpace) :
    (0<p 0 ∧ p 1^2+p 2^2+p 3^2<(p 0)^2) ↔
      ‖(WithLp.toLp 2 ![p 1,p 2,p 3] : EuclideanSpace ℝ (Fin 3))‖<p 0 := by
  let v : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![p 1,p 2,p 3]
  have hv : ‖v‖^2=p 1^2+p 2^2+p 3^2 := by
    simp [v,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_succ,add_assoc]
  change _ ↔ ‖v‖<p 0
  constructor
  · rintro ⟨ht,hr⟩
    nlinarith [norm_nonneg v]
  · intro h
    exact ⟨lt_of_le_of_lt (norm_nonneg v) h,by nlinarith [norm_nonneg v]⟩

end
end JinWishart
#print axioms JinWishart.twoRowTraceEquiv_det
#print axioms JinWishart.map_volume_twoRowTraceEquiv
#print axioms JinWishart.twoRowTraceCoordinates_cone
#print axioms JinWishart.twoRowTraceCone_iff_norm
