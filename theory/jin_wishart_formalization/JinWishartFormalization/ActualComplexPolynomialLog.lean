import JinWishartFormalization.ProperComplexGaussianPolynomialLog
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Log-L1 for holomorphic polynomials in the actual physical matrix entries.
Compressed determinants are polynomials in these COMPLEX entries, not in the
existing real-coordinate SampleIdx ring. Codex proofs. Real.log0=0 throughout.
[需人工审查] Physical variance, map-integrability and model correspondence.
-/
open Matrix MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

theorem integrable_actualComplexMatrix_holomorphic_negativeLog (m p : ℕ)
    (P : MvPolynomial (Fin m × Fin p) ℂ) :
    Integrable (fun z => complexNegativeLog (MvPolynomial.eval (complexMatrixEntries z) P))
      (stdGaussian (ComplexSample (m := m) (n := p))) := by
  have h := properComplex_pi_polynomial_negativeLog_integrable P
  rw [← complexMatrixEntries_law m p] at h
  exact (integrable_map_measure
    (measurable_const.max (MvPolynomial.continuous_eval P).norm.measurable.log.neg).aestronglyMeasurable
    (measurable_complexMatrixEntries m p).aemeasurable).mp h

theorem integrable_actualComplexMatrix_holomorphic_log (m p : ℕ)
    (P : MvPolynomial (Fin m × Fin p) ℂ) :
    Integrable (fun z => Real.log ‖MvPolynomial.eval (complexMatrixEntries z) P‖)
      (stdGaussian (ComplexSample (m := m) (n := p))) := by
  have h := properComplex_pi_polynomial_log_integrable P
  rw [← complexMatrixEntries_law m p] at h
  exact (integrable_map_measure (MvPolynomial.continuous_eval P).norm.measurable.log.aestronglyMeasurable
    (measurable_complexMatrixEntries m p).aemeasurable).mp h

def physicalEntryPolynomialMatrix (m p : ℕ) : Matrix (Fin m) (Fin p)
    (MvPolynomial (Fin m × Fin p) ℂ) := fun i j => MvPolynomial.X (i,j)

def entryAffineCompressedDet {m p n q : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (L : Matrix (Fin q) (Fin m) ℂ) (H : Matrix (Fin n) (Fin q) ℂ) :
    MvPolynomial (Fin m × Fin p) ℂ :=
  (L.map MvPolynomial.C *
    (physicalEntryPolynomialMatrix m p * B.map MvPolynomial.C + M.map MvPolynomial.C) *
    H.map MvPolynomial.C).det

theorem entryAffineCompressedDet_eval {m p n q : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (L : Matrix (Fin q) (Fin m) ℂ) (H : Matrix (Fin n) (Fin q) ℂ)
    (z : ComplexSample (m := m) (n := p)) :
    MvPolynomial.eval (complexMatrixEntries z) (entryAffineCompressedDet B M L H) =
      (L*(complexSampleMatrix z*B+M)*H).det := by
  let E := MvPolynomial.eval (complexMatrixEntries z)
  have hc {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) :
      (A.map (MvPolynomial.C : ℂ →+* MvPolynomial (Fin m × Fin p) ℂ)).map E = A := by
    ext i j
    simp [E]
  have hx : (physicalEntryPolynomialMatrix m p).map E = complexSampleMatrix z := by
    ext i j
    simp [E,complexMatrixEntries,physicalEntryPolynomialMatrix]
  unfold entryAffineCompressedDet
  rw [RingHom.map_det]
  change ((L.map MvPolynomial.C *
    (physicalEntryPolynomialMatrix m p * B.map MvPolynomial.C + M.map MvPolynomial.C) *
      H.map MvPolynomial.C).map E).det = _
  rw [Matrix.map_mul,Matrix.map_mul,Matrix.map_add,Matrix.map_mul]
  simp only [hc,hx]
  all_goals exact fun x y => map_add E x y

theorem integrable_actualAffineCompressedDet_negativeLog {m p n q : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (L : Matrix (Fin q) (Fin m) ℂ) (H : Matrix (Fin n) (Fin q) ℂ) :
    Integrable (fun z => complexNegativeLog (L*(complexSampleMatrix z*B+M)*H).det)
      (stdGaussian (ComplexSample (m := m) (n := p))) := by
  simpa only [entryAffineCompressedDet_eval] using
    integrable_actualComplexMatrix_holomorphic_negativeLog m p (entryAffineCompressedDet B M L H)

theorem integrable_actualAffineCompressedDet_log {m p n q : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (L : Matrix (Fin q) (Fin m) ℂ) (H : Matrix (Fin n) (Fin q) ℂ) :
    Integrable (fun z => Real.log ‖(L*(complexSampleMatrix z*B+M)*H).det‖)
      (stdGaussian (ComplexSample (m := m) (n := p))) := by
  simpa only [entryAffineCompressedDet_eval] using
    integrable_actualComplexMatrix_holomorphic_log m p (entryAffineCompressedDet B M L H)

end
end JinWishart
#print axioms JinWishart.integrable_actualComplexMatrix_holomorphic_negativeLog
#print axioms JinWishart.integrable_actualComplexMatrix_holomorphic_log
#print axioms JinWishart.entryAffineCompressedDet_eval
#print axioms JinWishart.integrable_actualAffineCompressedDet_negativeLog
#print axioms JinWishart.integrable_actualAffineCompressedDet_log
