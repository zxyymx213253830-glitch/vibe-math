import JinWishartFormalization.T3CentralTwoByTwoDensityInterface
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Basis.Fin

/-! Codex. Seed2026102408: 164 exact controls before source.
Trace/radius to ordered-eigenvalue linear density transport, not actual law yet.
[需人工审查] Direction of Jacobian and plane Lebesgue conventions. -/
open MeasureTheory Set
open scoped ENNReal
namespace JinWishart
noncomputable section

def traceRadiusEigenCoordinates (x : ℝ × ℝ) : ℝ × ℝ := (x.1+x.2,x.1-x.2)
def traceRadiusEigenInverse (y : ℝ × ℝ) : ℝ × ℝ := ((y.1+y.2)/2,(y.1-y.2)/2)

def traceRadiusEigenEquiv : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) where
  toFun := traceRadiusEigenCoordinates
  invFun := traceRadiusEigenInverse
  left_inv x := by ext <;> simp [traceRadiusEigenCoordinates,traceRadiusEigenInverse] <;> ring
  right_inv x := by ext <;> simp [traceRadiusEigenCoordinates,traceRadiusEigenInverse] <;> ring
  map_add' x y := by ext <;> simp [traceRadiusEigenCoordinates] <;> ring
  map_smul' a x := by ext <;> simp [traceRadiusEigenCoordinates] <;> ring

theorem traceRadiusEigenEquiv_det : traceRadiusEigenEquiv.toLinearMap.det=(-2 : ℝ) := by
  rw [← LinearMap.det_toMatrix (Basis.finTwoProd ℝ)]
  have hm : LinearMap.toMatrix (Basis.finTwoProd ℝ) (Basis.finTwoProd ℝ)
      traceRadiusEigenEquiv.toLinearMap=(!![(1:ℝ),1;1,-1] : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [LinearMap.toMatrix_apply,Basis.coe_finTwoProd_repr,traceRadiusEigenEquiv,
        traceRadiusEigenCoordinates]
  rw [hm,Matrix.det_fin_two]
  norm_num

theorem map_volume_traceRadiusEigenEquiv :
    (volume : Measure (ℝ × ℝ)).map traceRadiusEigenEquiv=(1/2 : ℝ≥0∞) • volume := by
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (ℝ × ℝ))
    (f := traceRadiusEigenEquiv.toLinearMap) (by rw [traceRadiusEigenEquiv_det];norm_num)
  simpa [traceRadiusEigenEquiv_det] using h

private def eigenMeasEquiv : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) :=
  traceRadiusEigenEquiv.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv

theorem traceRadiusEigen_density_transport (f : ℝ × ℝ → ℝ≥0∞) (hf : Measurable f) :
    ((volume : Measure (ℝ × ℝ)).withDensity f).map traceRadiusEigenCoordinates =
      volume.withDensity (fun y => (1/2 : ℝ≥0∞)*f (traceRadiusEigenInverse y)) := by
  have hmp : MeasurePreserving eigenMeasEquiv (volume : Measure (ℝ × ℝ))
      ((1/2 : ℝ≥0∞) • volume) := by
    refine ⟨eigenMeasEquiv.measurable,?_⟩
    change (volume : Measure (ℝ × ℝ)).map traceRadiusEigenEquiv= _
    exact map_volume_traceRadiusEigenEquiv
  have h := map_withDensity_measurePreserving eigenMeasEquiv volume
    ((1/2 : ℝ≥0∞) • volume) hmp f hf
  rw [withDensity_smul_measure,← withDensity_smul' (1/2) _ (by norm_num)] at h
  exact h

theorem traceRadiusDensity_spectral_transport :
    (((volume : Measure (ℝ × ℝ)).restrict {x | 0<x.2 ∧ x.2<x.1}).withDensity
      (fun x => ENNReal.ofReal (8*x.2^2*Real.exp (-2*x.1)))).map traceRadiusEigenCoordinates =
    volume.withDensity centralTwoByTwoPaperEigenvalueDensity := by
  let D : Set (ℝ × ℝ) := {x | 0<x.2 ∧ x.2<x.1}
  have hD : MeasurableSet D := by dsimp [D];measurability
  rw [← withDensity_indicator hD,
    traceRadiusEigen_density_transport _ ((by fun_prop).indicator hD)]
  congr 1
  funext y
  have hc : traceRadiusEigenInverse y ∈ D ↔ 0<y.2 ∧ y.2<y.1 := by
    change (0<(y.1-y.2)/2 ∧ (y.1-y.2)/2<(y.1+y.2)/2) ↔ _
    constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
  by_cases hy : 0<y.2 ∧ y.2<y.1
  · rw [Set.indicator_of_mem (hc.mpr hy)]
    change (1/2 : ℝ≥0∞)*ENNReal.ofReal
      (8*((y.1-y.2)/2)^2*Real.exp (-2*((y.1+y.2)/2)))= _
    rw [show (1/2 : ℝ≥0∞)=ENNReal.ofReal (1/2 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤1/2)]
    unfold centralTwoByTwoPaperEigenvalueDensity
    rw [if_pos hy]
    congr 1
    rw [show -2*((y.1+y.2)/2)=-(y.1+y.2) by ring]
    ring
  · rw [Set.indicator_of_notMem (fun h => hy (hc.mp h)),mul_zero]
    simp [centralTwoByTwoPaperEigenvalueDensity,hy]

end
end JinWishart
#print axioms JinWishart.traceRadiusEigenEquiv_det
#print axioms JinWishart.map_volume_traceRadiusEigenEquiv
#print axioms JinWishart.traceRadiusEigen_density_transport
#print axioms JinWishart.traceRadiusDensity_spectral_transport
