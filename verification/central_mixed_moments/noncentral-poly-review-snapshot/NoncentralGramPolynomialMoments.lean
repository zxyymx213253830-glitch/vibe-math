import JinWishartFormalization.GramDeterminantPolynomial

/-!
# Exact finite polynomial moments of an actual arbitrary-mean Gram matrix

Codex proofs. Deterministic means are substituted as polynomial constants.
This is not a noncentral minimum CDF or a joint spectral density theorem.
[需人工审查] Noncentral actual-model and variance correspondence.
-/
open Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace JinWishart
noncomputable section

def noncentralGramEntryPolynomial {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) (ComplexMatrixPolynomial m n) :=
  fun i j => ∑ k,
    (MvPolynomial.X (Sum.inr (k,i))+MvPolynomial.C (star (M k i))) *
      (MvPolynomial.X (Sum.inl (k,j))+MvPolynomial.C (M k j))

def noncentralShiftedGramDeterminantPolynomial {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (d : ℕ) (x : ℝ) : ComplexMatrixPolynomial m n :=
  (noncentralGramEntryPolynomial M +
    (MvPolynomial.C (x : ℂ) : ComplexMatrixPolynomial m n) • 1).det ^ d

theorem eval_noncentralGramEntryPolynomial {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (z : ComplexSample (m := m) (n := n)) (i j : Fin n) :
    complexGaussianPolynomialEval (noncentralGramEntryPolynomial M i j) (complexMatrixEntries z) =
      complexGram (complexSampleMatrix z+M) i j := by
  classical
  simp [complexGaussianPolynomialEval,noncentralGramEntryPolynomial,complexMatrixEntries,
    complexGram,Matrix.mul_apply,Matrix.conjTranspose_apply,map_add]

theorem eval_noncentralShiftedGramDeterminantPolynomial {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (d : ℕ) (x : ℝ)
    (z : ComplexSample (m := m) (n := n)) :
    complexGaussianPolynomialEval (noncentralShiftedGramDeterminantPolynomial M d x)
      (complexMatrixEntries z) = (complexGram (complexSampleMatrix z+M)+(x : ℂ) • 1).det ^ d := by
  classical
  let e := MvPolynomial.eval (Sum.elim (complexMatrixEntries z)
    (fun i => star (complexMatrixEntries z i)))
  change e ((noncentralGramEntryPolynomial M+
    (MvPolynomial.C (x : ℂ) : ComplexMatrixPolynomial m n) • 1).det ^ d) = _
  rw [map_pow,e.map_det]
  congr 2
  ext i j
  change e (noncentralGramEntryPolynomial M i j+
    ((MvPolynomial.C (x : ℂ) : ComplexMatrixPolynomial m n) •
    (1 : Matrix (Fin n) (Fin n) (ComplexMatrixPolynomial m n))) i j) = _
  rw [map_add]
  have h := eval_noncentralGramEntryPolynomial M z i j
  change e (noncentralGramEntryPolynomial M i j) = _ at h
  rw [h]
  simp [e,Matrix.smul_apply,Matrix.one_apply]
  split_ifs <;> simp

theorem integrable_actualNoncentral_shiftedGramDeterminant_power {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (d : ℕ) (x : ℝ) :
    Integrable (fun z => (complexGram (complexSampleMatrix z+M)+(x : ℂ) • 1).det ^ d)
      (stdGaussian (ComplexSample (m := m) (n := n))) := by
  have h := integrable_actualComplexMatrix_polynomial m n
    (noncentralShiftedGramDeterminantPolynomial M d x)
  simp_rw [eval_noncentralShiftedGramDeterminantPolynomial] at h
  exact h

theorem integral_actualNoncentral_shiftedGramDeterminant_power {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (d : ℕ) (x : ℝ) :
    (∫ z, (complexGram (complexSampleMatrix z+M)+(x : ℂ) • 1).det ^ d
      ∂stdGaussian (ComplexSample (m := m) (n := n))) =
        complexGaussianPolynomialMoment (noncentralShiftedGramDeterminantPolynomial M d x) := by
  have h := integral_actualComplexMatrix_polynomial m n
    (noncentralShiftedGramDeterminantPolynomial M d x)
  simp_rw [eval_noncentralShiftedGramDeterminantPolynomial] at h
  exact h

theorem integral_complexNoncentralWishart_shiftedDeterminant_power {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (d : ℕ) (x : ℝ) :
    (∫ A, (A+(x : ℂ) • 1).det ^ d ∂complexNoncentralWishart M) =
      complexGaussianPolynomialMoment (noncentralShiftedGramDeterminantPolynomial M d x) := by
  unfold complexNoncentralWishart
  rw [integral_map (measurable_shiftedComplexSampleGram M).aemeasurable
    (show Continuous (fun A : Matrix (Fin n) (Fin n) ℂ => (A+(x : ℂ) • 1).det ^ d)
      from by fun_prop).aestronglyMeasurable]
  exact integral_actualNoncentral_shiftedGramDeterminant_power M d x

end
end JinWishart
#print axioms JinWishart.eval_noncentralGramEntryPolynomial
#print axioms JinWishart.eval_noncentralShiftedGramDeterminantPolynomial
#print axioms JinWishart.integrable_actualNoncentral_shiftedGramDeterminant_power
#print axioms JinWishart.integral_actualNoncentral_shiftedGramDeterminant_power
#print axioms JinWishart.integral_complexNoncentralWishart_shiftedDeterminant_power
