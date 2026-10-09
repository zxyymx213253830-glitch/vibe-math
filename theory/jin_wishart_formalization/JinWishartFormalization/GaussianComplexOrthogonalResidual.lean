import JinWishartFormalization.GaussianComplexInnerProductLaw
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# Complex Gaussian projection and orthogonal residual

Reuse the existing jointly-Gaussian/zero-covariance independence theorem.
The direction is fixed and has norm one; no random QR frame is assumed.
[需人工审查] Joint Gaussian map, covariance and actual variance conventions.
-/

open MeasureTheory ProbabilityTheory

namespace JinWishart

noncomputable section

def complexOrthogonalResidual {m : ℕ} (a : ComplexColumnSpace m) :
    ComplexColumnSpace m →L[ℂ] ComplexColumnSpace m :=
  ContinuousLinearMap.id ℂ _ - (innerSL ℂ a).smulRight a

theorem complexOrthogonalResidual_apply {m : ℕ} (a z : ComplexColumnSpace m) :
    complexOrthogonalResidual a z = z - (inner ℂ a z) • a := rfl

theorem complexOrthogonalResidual_orthogonal {m : ℕ} (a z : ComplexColumnSpace m)
    (ha : ‖a‖ = 1) : inner ℂ a (complexOrthogonalResidual a z) = 0 := by
  simp [complexOrthogonalResidual_apply, inner_sub_right, inner_smul_right,
    inner_self_eq_norm_sq_to_K, ha]

theorem complexOrthogonalResidual_selfAdjoint_real {m : ℕ}
    (a y z : ComplexColumnSpace m) :
    inner ℝ y (complexOrthogonalResidual a z) =
      inner ℝ (complexOrthogonalResidual a y) z := by
  rw [complexColumn_real_inner, complexColumn_real_inner]
  simp [complexOrthogonalResidual_apply, inner_sub_right, inner_sub_left,
    inner_smul_right, inner_smul_left, inner_conj_symm, mul_comm]

/-- The missing diagonal Gram energy separates into projection and residual energies. -/
theorem complexOrthogonalResidual_norm_sq {m : ℕ} (a z : ComplexColumnSpace m)
    (ha : ‖a‖ = 1) :
    ‖z‖ ^ 2 = ‖inner ℂ a z‖ ^ 2 + ‖complexOrthogonalResidual a z‖ ^ 2 := by
  have hd : z = (inner ℂ a z) • a + complexOrthogonalResidual a z := by
    rw [complexOrthogonalResidual_apply]
    abel
  calc
    ‖z‖ ^ 2 = ‖(inner ℂ a z) • a + complexOrthogonalResidual a z‖ ^ 2 :=
      congrArg (fun v : ComplexColumnSpace m => ‖v‖ ^ 2) hd
    _ = _ := by
      rw [norm_add_sq (𝕜 := ℂ), inner_smul_left,
        complexOrthogonalResidual_orthogonal a z ha]
      simp [norm_smul, ha]

/-- Fixed complex Gaussian projection is independent of its entire residual vector. -/
theorem stdGaussian_complex_projection_indep_residual {m : ℕ}
    (a : ComplexColumnSpace m) (ha : ‖a‖ = 1) :
    IndepFun (fun z : ComplexColumnSpace m => inner ℂ a z)
      (fun z => complexOrthogonalResidual a z) (stdGaussian (ComplexColumnSpace m)) := by
  let L : ComplexColumnSpace m →L[ℝ] ℂ × ComplexColumnSpace m :=
    ((innerSL ℂ a).restrictScalars ℝ).prod
      ((complexOrthogonalResidual a).restrictScalars ℝ)
  have hG : HasGaussianLaw
      (fun z : ComplexColumnSpace m => (inner ℂ a z, complexOrthogonalResidual a z))
      (stdGaussian (ComplexColumnSpace m)) := by
    have hmap :=
      (IsGaussian.hasGaussianLaw_id (μ := stdGaussian (ComplexColumnSpace m))).map_of_measurable
        L (by fun_prop)
    apply hmap.congr
    exact Filter.Eventually.of_forall (fun z => by
      change L z = (inner ℂ a z, complexOrthogonalResidual a z)
      simp only [L, ContinuousLinearMap.prod_apply,
        ContinuousLinearMap.coe_restrictScalars', innerSL_apply_apply])
  apply hG.indepFun_of_covariance_inner
  intro x y
  have h1 : (fun z : ComplexColumnSpace m => inner ℝ x (inner ℂ a z)) =
      (fun z => inner ℝ (x • a) z) := by
    funext z
    rw [real_inner_comm, real_inner_complex_inner, real_inner_comm]
  have h2 : (fun z : ComplexColumnSpace m => inner ℝ y (complexOrthogonalResidual a z)) =
      (fun z => inner ℝ (complexOrthogonalResidual a y) z) := by
    funext z
    exact complexOrthogonalResidual_selfAdjoint_real a y z
  rw [h1, h2, ← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
    covarianceBilin_stdGaussian, innerSL_apply_apply, complexColumn_real_inner,
    inner_smul_left, complexOrthogonalResidual_orthogonal a y ha, mul_zero]
  rfl

/-- Transport actual independence through the explicit Gaussian column coordinates. -/
theorem indepFun_comp_complexColumnCoordinates {m : ℕ}
    (f : ComplexColumnSpace m → ℂ) (g : ComplexColumnSpace m → ComplexColumnSpace m)
    (hf : Measurable f) (hg : Measurable g)
    (h : IndepFun f g (stdGaussian (ComplexColumnSpace m))) :
    IndepFun (fun u => f (complexColumnCoordinates m u))
      (fun u => g (complexColumnCoordinates m u)) (stdGaussian (TwoColumnBlock m)) := by
  apply (indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)).2
  have hp := h.map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable
  have hc := stdGaussian_map (complexColumnCoordinates m)
  rw [← hc, Measure.map_map (hf.prodMk hg) (by fun_prop),
    Measure.map_map hf (by fun_prop), Measure.map_map hg (by fun_prop)] at hp
  exact hp

/-- Independence in the paper's actual circular variance-one complex columns. -/
theorem actualComplexColumn_projection_indep_residual {m : ℕ}
    (a : ComplexColumnSpace m) (ha : ‖a‖ = 1) :
    IndepFun (fun v : TwoColumnBlock m => inner ℂ a (actualComplexColumn v))
      (fun v => complexOrthogonalResidual a (actualComplexColumn v))
      (stdGaussian (TwoColumnBlock m)) := by
  have hi := (stdGaussian_complex_projection_indep_residual a ha).comp
    (φ := fun z : ℂ => (Real.sqrt 2)⁻¹ • z)
    (ψ := fun z : ComplexColumnSpace m => (Real.sqrt 2)⁻¹ • z)
    (by fun_prop) (by fun_prop)
  have hf : (fun z : ComplexColumnSpace m => inner ℂ a ((Real.sqrt 2)⁻¹ • z)) =
      (fun z => (Real.sqrt 2)⁻¹ • inner ℂ a z) := by
    funext z
    exact inner_smul_right_eq_smul _ _ _
  have hg : (fun z : ComplexColumnSpace m =>
      complexOrthogonalResidual a ((Real.sqrt 2)⁻¹ • z)) =
      (fun z => (Real.sqrt 2)⁻¹ • complexOrthogonalResidual a z) := by
    funext z
    exact ((complexOrthogonalResidual a).restrictScalars ℝ).map_smul _ _
  have hs : IndepFun (fun z : ComplexColumnSpace m => inner ℂ a ((Real.sqrt 2)⁻¹ • z))
      (fun z => complexOrthogonalResidual a ((Real.sqrt 2)⁻¹ • z))
      (stdGaussian (ComplexColumnSpace m)) := by
    rw [hf, hg]
    exact hi
  exact indepFun_comp_complexColumnCoordinates _ _ (by fun_prop) (by fun_prop) hs

/-- The actual projection and residual energy are independent, not merely uncorrelated. -/
theorem actualComplexColumn_projection_indep_residualEnergy {m : ℕ}
    (a : ComplexColumnSpace m) (ha : ‖a‖ = 1) :
    IndepFun (fun v : TwoColumnBlock m => inner ℂ a (actualComplexColumn v))
      (fun v => ‖complexOrthogonalResidual a (actualComplexColumn v)‖ ^ 2)
      (stdGaussian (TwoColumnBlock m)) :=
  (actualComplexColumn_projection_indep_residual a ha).comp
    (φ := id) (ψ := fun z : ComplexColumnSpace m => ‖z‖ ^ 2)
    measurable_id (by fun_prop)

/-- Product factorization of the actual full projection/residual law.
No candidate residual density is assumed. -/
theorem actualComplexColumn_projection_residual_joint_law {m : ℕ}
    (a : ComplexColumnSpace m) (ha : ‖a‖ = 1) :
    (stdGaussian (TwoColumnBlock m)).map
        (fun v => (inner ℂ a (actualComplexColumn v),
          complexOrthogonalResidual a (actualComplexColumn v))) =
      ((stdGaussian ℂ).map (fun z => (Real.sqrt 2)⁻¹ • z)).prod
        ((stdGaussian (TwoColumnBlock m)).map
          (fun v => complexOrthogonalResidual a (actualComplexColumn v))) := by
  have hm : Measurable (actualComplexColumn (m := m)) := by
    unfold actualComplexColumn
    fun_prop
  rw [(actualComplexColumn_projection_indep_residual a ha).map_prod_eq_prod_map_map
    (((innerSL ℂ a).continuous.measurable.comp hm).aemeasurable)
    (((complexOrthogonalResidual a).continuous.measurable.comp hm).aemeasurable),
    actualComplexColumn_inner_law, ha, mul_one]

end

end JinWishart
