import JinWishartFormalization.GaussianComplexFrameExists
import JinWishartFormalization.GaussianGramEnergyLaw

/-!
# Fixed complex unitary frames acting on all columns of an actual sample

Codex proofs. An explicit finite coordinate curry turns the same fixed complex
unitary on each column into a real linear isometry of the entire real Gaussian
source. Its pushforward preserves the ACTUAL central complex matrix law.
This file chooses no frame as a function of a random column and proves no
general Wishart density. [需人工审查] Coordinate curry, variance and future
use of fixed-frame invariance in the Gram-valued Bartlett fiber law.
-/

open Matrix MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

def matrixColumnIndexEquiv (m n : ℕ) :
    ((Fin m × Fin n) × Fin 2) ≃ (Σ _ : Fin n, Fin m × Fin 2) where
  toFun := fun p => ⟨p.1.2, p.1.1, p.2⟩
  invFun := fun q => ((q.2.1, q.1), q.2.2)
  left_inv := by intro p; rfl
  right_inv := by intro q; rfl

def complexSampleByColumns (m n : ℕ) :
    ComplexSample (m := m) (n := n) ≃ₗᵢ[ℝ]
      PiLp 2 (fun _ : Fin n => TwoColumnBlock m) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (matrixColumnIndexEquiv m n)).trans
    (LinearIsometryEquiv.piLpCurry ℝ 2 (fun (_ : Fin n) (_ : Fin m × Fin 2) => ℝ))

theorem complexSampleByColumns_apply {m n : ℕ}
    (z : ComplexSample (m := m) (n := n)) (j : Fin n) (i : Fin m) (k : Fin 2) :
    complexSampleByColumns m n z j (i, k) = z ((i, j), k) := by
  rfl

def encodedComplexMatrixFrame {m n : ℕ}
    (U : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) :
    ComplexSample (m := m) (n := n) ≃ₗᵢ[ℝ] ComplexSample (m := m) (n := n) :=
  (complexSampleByColumns m n).trans
    ((LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Fin n => encodedComplexFrame U)).trans
      (complexSampleByColumns m n).symm)

theorem encodedComplexMatrixFrame_gaussianLaw {m n : ℕ}
    (U : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) :
    (stdGaussian (ComplexSample (m := m) (n := n))).map (encodedComplexMatrixFrame U) =
      stdGaussian (ComplexSample (m := m) (n := n)) :=
  stdGaussian_map _

theorem complexSampleByColumns_encoded_frame {m n : ℕ}
    (U : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m))
    (z : ComplexSample (m := m) (n := n)) (j : Fin n) :
    complexColumnCoordinates m (complexSampleByColumns m n (encodedComplexMatrixFrame U z) j) =
      U (complexColumnCoordinates m (complexSampleByColumns m n z j)) := by
  simp only [encodedComplexMatrixFrame, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.piLpCongrRight_apply,
    PiLp.toLp_apply]
  exact complexColumnCoordinates_encodedFrame U _

def complexMatrixColumn {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (j : Fin n) :
    EuclideanSpace ℂ (Fin m) := WithLp.toLp 2 (fun i => A i j)

theorem complexSampleMatrix_column_coordinates {m n : ℕ}
    (z : ComplexSample (m := m) (n := n)) (j : Fin n) :
    complexMatrixColumn (complexSampleMatrix z) j =
      (Real.sqrt 2)⁻¹ • complexColumnCoordinates m (complexSampleByColumns m n z j) := by
  ext i
  change ((z ((i, j), 0) : ℂ) + Complex.I * z ((i, j), 1)) / (Real.sqrt 2 : ℂ) =
    (Real.sqrt (2 : ℝ))⁻¹ • ((z ((i, j), 0) : ℂ) + z ((i, j), 1) * Complex.I)
  simp only [Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
  ring

def unitaryActColumns {m n : ℕ}
    (U : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m))
    (A : Matrix (Fin m) (Fin n) ℂ) : Matrix (Fin m) (Fin n) ℂ :=
  fun i j => U (complexMatrixColumn A j) i

theorem measurable_unitaryActColumns {m n : ℕ}
    (U : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) :
    Measurable (unitaryActColumns (n := n) U) := by
  unfold unitaryActColumns complexMatrixColumn
  fun_prop

theorem complexSampleMatrix_encoded_frame {m n : ℕ}
    (U : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m))
    (z : ComplexSample (m := m) (n := n)) :
    complexSampleMatrix (encodedComplexMatrixFrame U z) =
      unitaryActColumns U (complexSampleMatrix z) := by
  ext i j
  have hleft := complexSampleMatrix_column_coordinates (encodedComplexMatrixFrame U z) j
  have hright := complexSampleMatrix_column_coordinates z j
  rw [complexSampleByColumns_encoded_frame] at hleft
  have hsmul := (complexFrameToReal U).map_smul (Real.sqrt 2)⁻¹
    (complexColumnCoordinates m (complexSampleByColumns m n z j))
  have hcol : complexMatrixColumn (complexSampleMatrix (encodedComplexMatrixFrame U z)) j =
      U (complexMatrixColumn (complexSampleMatrix z) j) := by
    rw [hleft, hright]
    exact hsmul.symm
  exact congrArg (fun v : EuclideanSpace ℂ (Fin m) => v i) hcol

/-- The full central matrix law, rather than only one column or its energy. -/
theorem complexGaussianMatrixLaw_unitary_invariant {m n : ℕ}
    (U : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m)) :
    (complexGaussianMatrixLaw (0 : Matrix (Fin m) (Fin n) ℂ)).map (unitaryActColumns U) =
      complexGaussianMatrixLaw (0 : Matrix (Fin m) (Fin n) ℂ) := by
  let g : ComplexSample (m := m) (n := n) → Matrix (Fin m) (Fin n) ℂ :=
    fun z => complexSampleMatrix z + 0
  have hg : Measurable g := measurable_shiftedComplexSampleMatrix _
  change ((stdGaussian (ComplexSample (m := m) (n := n))).map g).map
    (unitaryActColumns U) = (stdGaussian (ComplexSample (m := m) (n := n))).map g
  rw [Measure.map_map (measurable_unitaryActColumns U) hg]
  have hfun : unitaryActColumns U ∘ g = g ∘ encodedComplexMatrixFrame U := by
    funext z
    simp only [g, Function.comp_def, add_zero, complexSampleMatrix_encoded_frame]
  rw [hfun, ← Measure.map_map hg (encodedComplexMatrixFrame U).continuous.measurable,
    encodedComplexMatrixFrame_gaussianLaw]

theorem complexGram_unitaryActColumns {m n : ℕ}
    (U : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m))
    (A : Matrix (Fin m) (Fin n) ℂ) :
    complexGram (unitaryActColumns U A) = complexGram A := by
  ext j k
  have h := U.inner_map_map (complexMatrixColumn A j) (complexMatrixColumn A k)
  simpa only [complexGram, Matrix.mul_apply, Matrix.conjTranspose_apply,
    unitaryActColumns, complexMatrixColumn, PiLp.inner_apply, RCLike.inner_apply,
    Complex.inner, RCLike.star_def, mul_comm] using h

end
end JinWishart

#print axioms JinWishart.complexSampleByColumns_apply
#print axioms JinWishart.encodedComplexMatrixFrame_gaussianLaw
#print axioms JinWishart.complexSampleByColumns_encoded_frame
#print axioms JinWishart.complexSampleMatrix_column_coordinates
#print axioms JinWishart.measurable_unitaryActColumns
#print axioms JinWishart.complexSampleMatrix_encoded_frame
#print axioms JinWishart.complexGaussianMatrixLaw_unitary_invariant
#print axioms JinWishart.complexGram_unitaryActColumns
