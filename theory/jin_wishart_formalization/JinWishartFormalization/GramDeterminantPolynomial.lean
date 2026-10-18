import JinWishartFormalization.GaussianMatrixPolynomialLaw
import JinWishartFormalization.CentralWishartMinimumBridge

/-!
# Explicit polynomial representing a shifted Gram determinant power

Codex proofs. The factorial functional integrates the actual Gaussian source.
[需人工审查] Actual-source/model correspondence; no spectral law assumed.
-/
open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace JinWishart
noncomputable section

abbrev ComplexMatrixPolynomial (m n : ℕ) :=
  MvPolynomial ((Fin m × Fin n) ⊕ (Fin m × Fin n)) ℂ

def gramEntryPolynomial (m n : ℕ) : Matrix (Fin n) (Fin n) (ComplexMatrixPolynomial m n) :=
  fun i j => ∑ k, MvPolynomial.X (Sum.inr (k,i)) * MvPolynomial.X (Sum.inl (k,j))

def shiftedGramDeterminantPolynomial (m n d : ℕ) (x : ℝ) : ComplexMatrixPolynomial m n :=
  (gramEntryPolynomial m n + (MvPolynomial.C (x : ℂ) : ComplexMatrixPolynomial m n) • 1).det ^ d

theorem eval_gramEntryPolynomial (m n : ℕ)
    (z : ComplexSample (m := m) (n := n)) (i j : Fin n) :
    complexGaussianPolynomialEval (gramEntryPolynomial m n i j) (complexMatrixEntries z) =
      complexSampleGram z i j := by
  classical
  simp [complexGaussianPolynomialEval,gramEntryPolynomial,complexMatrixEntries,
    complexSampleGram,complexGram,Matrix.mul_apply,Matrix.conjTranspose_apply]

theorem eval_shiftedGramDeterminantPolynomial (m n d : ℕ) (x : ℝ)
    (z : ComplexSample (m := m) (n := n)) :
    complexGaussianPolynomialEval (shiftedGramDeterminantPolynomial m n d x)
      (complexMatrixEntries z) = (complexSampleGram z+(x : ℂ) • 1).det ^ d := by
  classical
  let e := MvPolynomial.eval (Sum.elim (complexMatrixEntries z)
    (fun i => star (complexMatrixEntries z i)))
  change e ((gramEntryPolynomial m n+(MvPolynomial.C (x : ℂ) : ComplexMatrixPolynomial m n) • 1).det ^ d) = _
  rw [map_pow,e.map_det]
  congr 2
  ext i j
  change e (gramEntryPolynomial m n i j+(((MvPolynomial.C (x : ℂ) : ComplexMatrixPolynomial m n)) •
    (1 : Matrix (Fin n) (Fin n) (ComplexMatrixPolynomial m n))) i j) = _
  rw [map_add]
  have h := eval_gramEntryPolynomial m n z i j
  change e (gramEntryPolynomial m n i j) = _ at h
  rw [h]
  simp [e,Matrix.smul_apply,Matrix.one_apply]
  split_ifs <;> simp

theorem integrable_actual_shiftedGramDeterminant_power (m n d : ℕ) (x : ℝ) :
    Integrable (fun z => (complexSampleGram z+(x : ℂ) • 1).det ^ d)
      (stdGaussian (ComplexSample (m := m) (n := n))) := by
  have h := integrable_actualComplexMatrix_polynomial m n
    (shiftedGramDeterminantPolynomial m n d x)
  simp_rw [eval_shiftedGramDeterminantPolynomial] at h
  exact h

theorem integral_actual_shiftedGramDeterminant_power (m n d : ℕ) (x : ℝ) :
    (∫ z, (complexSampleGram z+(x : ℂ) • 1).det ^ d
      ∂stdGaussian (ComplexSample (m := m) (n := n))) =
        complexGaussianPolynomialMoment (shiftedGramDeterminantPolynomial m n d x) := by
  have h := integral_actualComplexMatrix_polynomial m n
    (shiftedGramDeterminantPolynomial m n d x)
  simp_rw [eval_shiftedGramDeterminantPolynomial] at h
  exact h

end
end JinWishart
#print axioms JinWishart.eval_gramEntryPolynomial
#print axioms JinWishart.eval_shiftedGramDeterminantPolynomial
#print axioms JinWishart.integrable_actual_shiftedGramDeterminant_power
#print axioms JinWishart.integral_actual_shiftedGramDeterminant_power
