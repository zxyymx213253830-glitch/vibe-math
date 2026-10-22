import JinWishartFormalization.CanonicalFinBlockComparison
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! Actual proper-CN1 shifted matrix shear factors have every nonnegative real moment.
The left factor Q is fixed and may be singular or zero. No random inverse N is used.
[需人工审查] Inherited Gaussian measure/model, and subsequent joint inverse-moment transport. -/
open Matrix MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

private def sampleRealLinear (c b : ℕ) :
    ComplexSample (m := c) (n := b) →ₗ[ℝ] Matrix (Fin c) (Fin b) ℂ where
  toFun := complexSampleMatrix
  map_add' := by
    intro x y
    ext i j
    simp only [Matrix.add_apply,complexSampleMatrix,PiLp.add_apply,Complex.ofReal_add]
    ring
  map_smul' := by
    intro a z
    ext i j
    simp [complexSampleMatrix,PiLp.smul_apply,smul_eq_mul,Complex.ofReal_mul]
    ring

private def leftOperatorLinear {c b : ℕ} (Q : Matrix (Fin c) (Fin c) ℂ) :
    Matrix (Fin c) (Fin b) ℂ →ₗ[ℂ]
      (EuclideanSpace ℂ (Fin b) →L[ℂ] EuclideanSpace ℂ (Fin c)) where
  toFun X := (Matrix.toEuclideanLin (Q*X)).toContinuousLinearMap
  map_add' := by
    intro X Y
    simp only [Matrix.mul_add,map_add]
  map_smul' := by
    intro a X
    simp only [Matrix.mul_smul,map_smul,RingHom.id_apply]

theorem integrable_actual_canonical_shear_factor {c b : ℕ}
    (Q : Matrix (Fin c) (Fin c) ℂ) (M : Matrix (Fin c) (Fin b) ℂ)
    (q : ℝ) (hq : 0≤q) :
    Integrable (fun z : ComplexSample (m := c) (n := b) =>
      (1+‖(Matrix.toEuclideanLin (Q*(complexSampleMatrix z+M))).toContinuousLinearMap‖)^q)
      (stdGaussian (ComplexSample (m := c) (n := b))) := by
  let μ := stdGaussian (ComplexSample (m := c) (n := b))
  let r := ENNReal.ofReal q
  let F := leftOperatorLinear (b := b) Q
  let L := ((F.restrictScalars ℝ).comp (sampleRealLinear c b)).toContinuousLinearMap
  have hraw : MemLp (id : ComplexSample (m := c) (n := b) → _) r μ :=
    IsGaussian.memLp_id μ r (by simp [r])
  have hL := hraw.continuousLinearMap_comp L
  have hW : MemLp (fun z : ComplexSample (m := c) (n := b) =>
      (Matrix.toEuclideanLin (Q*(complexSampleMatrix z+M))).toContinuousLinearMap) r μ := by
    convert hL.add (memLp_const (F M)) using 1
    funext z
    change (Matrix.toEuclideanLin (Q*(complexSampleMatrix z+M))).toContinuousLinearMap=
      (Matrix.toEuclideanLin (Q*complexSampleMatrix z)).toContinuousLinearMap+F M
    simp only [Matrix.mul_add,map_add]
    rfl
  have hG : MemLp (fun z : ComplexSample (m := c) (n := b) =>
      1+‖(Matrix.toEuclideanLin (Q*(complexSampleMatrix z+M))).toContinuousLinearMap‖) r μ :=
    (memLp_const (1 : ℝ)).add hW.norm
  have hp := hG.integrable_norm_rpow'
  convert hp using 1
  funext z
  rw [ENNReal.toReal_ofReal hq]
  rw [Real.norm_of_nonneg (by positivity)]

end
end JinWishart
#print axioms JinWishart.integrable_actual_canonical_shear_factor
