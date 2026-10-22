import JinWishartFormalization.JointKernelCanonicalNormalization
import JinWishartFormalization.ProperGaussianAdjointLaw
import JinWishartFormalization.GaussianOrthogonalProjectionLaw

/-! Full proper-CN1 matrix law under a fixed rectangular isometric projection.
Codex. A complex isometry is realified before using the existing coisometry
Gaussian law. Source variance scaling remains explicit.
[需人工审查] Coordinate and actual-law transport; future block independence. -/
open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace JinWishart
noncomputable section

private theorem euclideanRealInner {ι : Type*} [Fintype ι]
    (x y : EuclideanSpace ℂ ι) : inner ℝ x y=(inner ℂ x y).re := by
  simp only [PiLp.inner_apply]
  change (∑ i,inner ℝ (x i) (y i))=Complex.reCLM (∑ i,inner ℂ (x i) (y i))
  rw [map_sum]
  rfl

theorem stdGaussian_complex_isometry_adjoint_law
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (U : EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ) :
    (stdGaussian (EuclideanSpace ℂ κ)).map U.adjoint =
      stdGaussian (EuclideanSpace ℂ ι) := by
  let R : EuclideanSpace ℂ ι →ₗᵢ[ℝ] EuclideanSpace ℂ κ :=
    { toLinearMap := U.toLinearMap.restrictScalars ℝ
      norm_map' := U.norm_map }
  have he : (R.adjoint : EuclideanSpace ℂ κ → EuclideanSpace ℂ ι)=U.adjoint := by
    funext x
    apply ext_inner_right ℝ
    intro y
    rw [LinearMap.adjoint_inner_left]
    change inner ℝ x (U y)=inner ℝ (U.adjoint x) y
    rw [euclideanRealInner,euclideanRealInner,
      LinearMap.adjoint_inner_left]
    rfl
  let A := R.toLinearMap.toContinuousLinearMap
  have h := stdGaussian_map_adjoint_norm_preserving A.adjoint (fun t => by
    rw [ContinuousLinearMap.adjoint_adjoint]
    exact R.norm_map t)
  change (stdGaussian (EuclideanSpace ℂ κ)).map R.adjoint = _ at h
  simpa only [he] using h

private def matrixGaussianCoordinates (m n : ℕ) :
    ComplexSample (m := m) (n := n) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin m × Fin n) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (Equiv.sigmaEquivProd (Fin m × Fin n) (Fin 2)).symm).trans
      (Pi.orthonormalBasis (fun _ : Fin m × Fin n => Complex.orthonormalBasisOneI)).repr.symm

private theorem matrixLawCoordinates (m n : ℕ) :
    complexGaussianMatrixLaw (0 : Matrix (Fin m) (Fin n) ℂ)=
      (stdGaussian (EuclideanSpace ℂ (Fin m × Fin n))).map
        (fun x i j => (((Real.sqrt 2 : ℂ)⁻¹) • x) (i,j)) := by
  unfold complexGaussianMatrixLaw
  have he : (fun z : ComplexSample (m := m) (n := n) => complexSampleMatrix z+0)=
      (fun (x : EuclideanSpace ℂ (Fin m × Fin n)) i j =>
        (((Real.sqrt 2 : ℂ)⁻¹) • x) (i,j)) ∘ matrixGaussianCoordinates m n := by
    funext z
    ext i j
    change ((z ((i,j),0) : ℂ)+Complex.I*z ((i,j),1))/(Real.sqrt 2 : ℂ)+0 =
      (Real.sqrt 2 : ℂ)⁻¹*((z ((i,j),0) : ℂ)+z ((i,j),1)*Complex.I)
    ring
  erw [he,← Measure.map_map (by fun_prop) (matrixGaussianCoordinates m n).continuous.measurable,
    stdGaussian_map]
  rfl

private def columnLiftLinear {p b : ℕ}
    (U : EuclideanSpace ℂ (Fin b) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin p)) (n : ℕ) :
    EuclideanSpace ℂ (Fin b × Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin p × Fin n) where
  toFun x := WithLp.toLp 2 (fun ij => U (WithLp.toLp 2 (fun k => x (k,ij.2))) ij.1)
  map_add' x y := by
    ext i
    change U (WithLp.toLp 2 (fun k => x (k,i.2)+y (k,i.2))) i.1 = _
    change U (WithLp.toLp 2 (fun k => x (k,i.2))+
      WithLp.toLp 2 (fun k => y (k,i.2))) i.1 = _
    rw [map_add]
    rfl
  map_smul' c x := by
    ext i
    change U (c • WithLp.toLp 2 (fun k => x (k,i.2))) i.1 = _
    rw [map_smul]
    rfl

private def columnLift {p b : ℕ}
    (U : EuclideanSpace ℂ (Fin b) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin p)) (n : ℕ) :
    EuclideanSpace ℂ (Fin b × Fin n) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin p × Fin n) :=
  (columnLiftLinear U n).isometryOfInner (by
    intro x y
    simp only [PiLp.inner_apply,Fintype.sum_prod_type]
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    exact U.inner_map_map (WithLp.toLp 2 (fun i => x (i,j)))
      (WithLp.toLp 2 (fun i => y (i,j))))

private theorem columnLift_adjoint {p b n : ℕ}
    (U : EuclideanSpace ℂ (Fin b) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin p))
    (x : EuclideanSpace ℂ (Fin p × Fin n)) :
    (columnLift U n).adjoint x=WithLp.toLp 2
      (fun ij => U.adjoint (WithLp.toLp 2 (fun k => x (k,ij.2))) ij.1) := by
  apply ext_inner_left ℂ
  intro y
  rw [LinearMap.adjoint_inner_right]
  simp only [PiLp.inner_apply,Fintype.sum_prod_type]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  exact (U.toLinearMap.adjoint_inner_right (WithLp.toLp 2 (fun i => y (i,j)))
    (WithLp.toLp 2 (fun i => x (i,j)))).symm

theorem complexGaussianMatrixLaw_rectangular_column_projection {p b n : ℕ}
    (U : EuclideanSpace ℂ (Fin b) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin p)) :
    (complexGaussianMatrixLaw (0 : Matrix (Fin p) (Fin n) ℂ)).map
      (fun A i j => U.adjoint (complexMatrixColumn A j) i)=
        complexGaussianMatrixLaw (0 : Matrix (Fin b) (Fin n) ℂ) := by
  erw [matrixLawCoordinates p n,matrixLawCoordinates b n,
    Measure.map_map (by unfold complexMatrixColumn; fun_prop) (by fun_prop)]
  have he : (fun (A : Matrix (Fin p) (Fin n) ℂ) i j =>
      U.adjoint (complexMatrixColumn A j) i) ∘
      (fun (x : EuclideanSpace ℂ (Fin p × Fin n)) i j =>
        (((Real.sqrt 2 : ℂ)⁻¹) • x) (i,j)) =
      (fun (x : EuclideanSpace ℂ (Fin b × Fin n)) i j =>
        (((Real.sqrt 2 : ℂ)⁻¹) • x) (i,j)) ∘ (columnLift U n).adjoint := by
    funext x
    ext i j
    change U.adjoint ((Real.sqrt 2 : ℂ)⁻¹ • WithLp.toLp 2 (fun k => x (k,j))) i = _
    rw [map_smul]
    change (((Real.sqrt 2 : ℂ)⁻¹) • U.adjoint (WithLp.toLp 2 (fun k => x (k,j)))) i =
      ((((Real.sqrt 2 : ℂ)⁻¹) • (columnLift U n).adjoint x) (i,j))
    rw [columnLift_adjoint]
    rfl
  erw [he,← Measure.map_map (by fun_prop) (by fun_prop),
    stdGaussian_complex_isometry_adjoint_law]

theorem complexGaussianMatrixLaw_right_isometric_projection {m p b : ℕ}
    (U : Matrix (Fin p) (Fin b) ℂ) (hU : Uᴴ*U=1) :
    (complexGaussianMatrixLaw (0 : Matrix (Fin m) (Fin p) ℂ)).map
      (fun Z => Z*U)=complexGaussianMatrixLaw (0 : Matrix (Fin m) (Fin b) ℂ) := by
  have hi : U.toEuclideanLin.adjoint.comp U.toEuclideanLin=LinearMap.id := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    have h := congrArg Matrix.toEuclideanLin hU
    simpa only [Matrix.toEuclideanLin,Matrix.toLpLin_mul_same,Matrix.toLpLin_one] using h
  let f := U.toEuclideanLin.isometryOfInner (by
    intro y z
    calc
      inner ℂ (U.toEuclideanLin y) (U.toEuclideanLin z)=
          inner ℂ y (U.toEuclideanLin.adjoint (U.toEuclideanLin z)) :=
        (U.toEuclideanLin.adjoint_inner_right y (U.toEuclideanLin z)).symm
      _ = inner ℂ y z := congrArg (inner ℂ y) (LinearMap.congr_fun hi z))
  have hp := complexGaussianMatrixLaw_rectangular_column_projection (n := m) f
  have he : (fun (A : Matrix (Fin p) (Fin m) ℂ) i j =>
      f.adjoint (complexMatrixColumn A j) i)=(fun A => Uᴴ*A) := by
    funext A
    ext i j
    change U.toEuclideanLin.adjoint (WithLp.toLp 2 (fun k => A k j)) i=(Uᴴ*A) i j
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    rfl
  rw [he] at hp
  have heq : (fun Z : Matrix (Fin m) (Fin p) ℂ => Z*U)=
      Matrix.conjTranspose ∘ (fun A => Uᴴ*A) ∘ Matrix.conjTranspose := by
    funext Z
    simp only [Function.comp_def,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
  have ha : Measurable (Matrix.conjTranspose : Matrix (Fin m) (Fin p) ℂ →
      Matrix (Fin p) (Fin m) ℂ) := by fun_prop
  have hb : Measurable (fun A : Matrix (Fin p) (Fin m) ℂ => Uᴴ*A) :=
    (continuous_const.matrix_mul continuous_id).measurable
  have hc : Measurable (Matrix.conjTranspose : Matrix (Fin b) (Fin m) ℂ →
      Matrix (Fin m) (Fin b) ℂ) := by fun_prop
  rw [heq,← Measure.map_map hc (hb.comp ha),
    ← Measure.map_map hb ha,
    complexGaussianMatrixLaw_conjTranspose,Matrix.conjTranspose_zero,hp,
    complexGaussianMatrixLaw_conjTranspose,Matrix.conjTranspose_zero]

end
end JinWishart
#print axioms JinWishart.stdGaussian_complex_isometry_adjoint_law
#print axioms JinWishart.complexGaussianMatrixLaw_rectangular_column_projection

#print axioms JinWishart.complexGaussianMatrixLaw_right_isometric_projection
