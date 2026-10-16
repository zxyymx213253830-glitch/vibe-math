import JinWishartFormalization.CentralHermitianCoordinates
import JinWishartFormalization.TwoRowActualNormalizedDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Coordinate and Frobenius normalizations for Hermitian matrices

The energy here is the sum of squared complex entry norms, not the default
supremum norm of `Matrix`. We prove the dimension-independent coordinate
energy identity, an explicit orthonormal-coordinate normalization in size two,
and re-express the actual Gram density relative to that frame volume.
[需人工审查] Identification with the intrinsic Frobenius subspace volume;
the statements below expose the explicit frame map and its normalization.
Numerical/symbolic preflight: hermitian_coordinate_metric_control.py.
-/

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace JinWishart
noncomputable section

def hermitianFrobeniusEnergy {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ∑ i, ∑ j, ‖A i j‖ ^ 2

theorem hermitianCoordinate_entry_energy {n : ℕ}
    (q : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    ‖hermitianOfRealCoordinates q i j‖ ^ 2 =
      q i j ^ 2 + (if i = j then 0 else q j i ^ 2) := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  by_cases he : i = j
  · subst j
    simp [hermitianOfRealCoordinates] <;> ring
  · by_cases hl : i < j
    · simp [hermitianOfRealCoordinates, he, hl] <;> ring
    · simp [hermitianOfRealCoordinates, he, hl] <;> ring

/-- Every off-diagonal real coordinate is counted twice in Frobenius energy. -/
theorem hermitianCoordinate_frobeniusEnergy {n : ℕ}
    (q : Matrix (Fin n) (Fin n) ℝ) :
    hermitianFrobeniusEnergy (hermitianOfRealCoordinates q) =
      ∑ i, ∑ j, (if i = j then (1 : ℝ) else 2) * q i j ^ 2 := by
  have hs : (∑ i, ∑ j, (if i = j then (0 : ℝ) else q j i ^ 2)) =
      ∑ i, ∑ j, (if i = j then (0 : ℝ) else q i j ^ 2) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    by_cases he : i = j
    · subst j
      simp
    · simp [he, Ne.symm he]
  unfold hermitianFrobeniusEnergy
  simp_rw [hermitianCoordinate_entry_energy, Finset.sum_add_distrib]
  rw [hs, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases he : i = j <;> simp [he] <;> ring

def twoRowCoordinatesAsSquare (q : GramChartSpace) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![q 0, q 1; q 2, q 3]

theorem twoRow_hermitian_frobeniusEnergy (q : GramChartSpace) :
    hermitianFrobeniusEnergy (hermitianOfRealCoordinates (twoRowCoordinatesAsSquare q)) =
      q 0 ^ 2 + 2 * q 1 ^ 2 + 2 * q 2 ^ 2 + q 3 ^ 2 := by
  rw [hermitianCoordinate_frobeniusEnergy]
  simp [Fin.sum_univ_two, twoRowCoordinatesAsSquare] <;> ring

def twoRowInverseFrobeniusMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![1, (Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹, 1]

theorem twoRowInverseFrobenius_det : twoRowInverseFrobeniusMatrix.det = (2 : ℝ)⁻¹ := by
  simp [twoRowInverseFrobeniusMatrix, Matrix.det_diagonal, Fin.prod_univ_succ,
    ← mul_inv, Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

theorem twoRowInverseFrobenius_apply (q : GramChartSpace) :
    Matrix.toLin' twoRowInverseFrobeniusMatrix q =
      ![q 0, (Real.sqrt 2)⁻¹ * q 1, (Real.sqrt 2)⁻¹ * q 2, q 3] := by
  change twoRowInverseFrobeniusMatrix.mulVec q = _
  ext i
  fin_cases i <;> simp [twoRowInverseFrobeniusMatrix, Matrix.diagonal_mulVec]

/-- The rescaled coordinates have ordinary Euclidean squared energy. -/
theorem twoRow_inverseFrame_frobeniusEnergy (q : GramChartSpace) :
    hermitianFrobeniusEnergy (hermitianOfRealCoordinates
      (twoRowCoordinatesAsSquare (Matrix.toLin' twoRowInverseFrobeniusMatrix q))) =
        q 0 ^ 2 + q 1 ^ 2 + q 2 ^ 2 + q 3 ^ 2 := by
  have hi : 2 * ((Real.sqrt 2)⁻¹) ^ 2 = 1 := by
    rw [inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hs (x : ℝ) : 2 * ((Real.sqrt 2)⁻¹ * x) ^ 2 = x ^ 2 := by
    rw [mul_pow, ← mul_assoc, hi, one_mul]
  rw [twoRow_hermitian_frobeniusEnergy, twoRowInverseFrobenius_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, hs]

/-- Volume in coordinates obtained from the displayed Frobenius-normalized frame. -/
def twoRowFrobeniusFrameVolume : Measure GramChartSpace :=
  (volume : Measure GramChartSpace).map (Matrix.toLin' twoRowInverseFrobeniusMatrix)

theorem twoRowFrobeniusFrameVolume_eq_two_smul :
    twoRowFrobeniusFrameVolume = (2 : ℝ≥0∞) • (volume : Measure GramChartSpace) := by
  unfold twoRowFrobeniusFrameVolume
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi
    (by rw [twoRowInverseFrobenius_det]; norm_num), twoRowInverseFrobenius_det]
  norm_num

/-- Actual density under the normalized-frame volume has coefficient (2*pi)^-1.
This is a reference-measure conversion of the existing actual law. -/
theorem actualTwoRow_Gram_frobeniusFrameDensity :
    (complexWishart (m := 2) (n := 2)).map twoRowGramRealCoordinates =
      (twoRowFrobeniusFrameVolume.restrict {q : GramChartSpace |
        0 < q 0 ∧ q 1 ^ 2 + q 2 ^ 2 < q 0 * q 3}).withDensity
        (fun q => ENNReal.ofReal ((2 * Real.pi)⁻¹ * Real.exp (-(q 0 + q 3)))) := by
  rw [complexWishart_twoRow_realCoordinates_eq_traceDensity,
    twoRowFrobeniusFrameVolume_eq_two_smul, Measure.restrict_smul,
    withDensity_smul_measure, ← withDensity_smul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  apply withDensity_congr_ae
  filter_upwards with q
  change ENNReal.ofReal (Real.pi⁻¹ * Real.exp (-(q 0 + q 3))) =
    2 * ENNReal.ofReal ((2 * Real.pi)⁻¹ * Real.exp (-(q 0 + q 3)))
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  field_simp [Real.pi_ne_zero] <;> ring

end
end JinWishart

#print axioms JinWishart.hermitianCoordinate_entry_energy
#print axioms JinWishart.hermitianCoordinate_frobeniusEnergy
#print axioms JinWishart.twoRow_hermitian_frobeniusEnergy
#print axioms JinWishart.twoRowInverseFrobenius_det
#print axioms JinWishart.twoRowInverseFrobenius_apply
#print axioms JinWishart.twoRow_inverseFrame_frobeniusEnergy
#print axioms JinWishart.twoRowFrobeniusFrameVolume_eq_two_smul
#print axioms JinWishart.actualTwoRow_Gram_frobeniusFrameDensity
