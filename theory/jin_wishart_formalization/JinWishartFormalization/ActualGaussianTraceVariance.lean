import JinWishartFormalization.NoncentralGramSecondMomentClosed
import JinWishartFormalization.ComplexGaussianTotalEnergyMoment

/-! Exact ACTUAL second moment of the trace, distinct from trace of the square.
Codex. [需人工审查] Gaussian transport, real integral and variance interpretation.
-/
open Matrix MeasureTheory ProbabilityTheory
open scoped ComplexOrder
namespace JinWishart
noncomputable section

theorem complexTotalEnergyPolynomial_eq_Gram_trace {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) :
    complexTotalEnergyPolynomial (fun ij : Fin m × Fin n => M ij.1 ij.2) =
      (noncentralGramEntryPolynomial M).trace := by
  classical
  simp only [complexTotalEnergyPolynomial,Fintype.sum_prod_type,Matrix.trace,Matrix.diag,
    noncentralGramEntryPolynomial]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem eval_complexTotalEnergyPolynomial_sq {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (z : ComplexSample (m := m) (n := n)) :
    complexGaussianPolynomialEval
      (complexTotalEnergyPolynomial (fun ij : Fin m × Fin n => M ij.1 ij.2)^2) (complexMatrixEntries z) =
      ((complexGram (complexSampleMatrix z+M)).trace)^2 := by
  classical
  let e := MvPolynomial.eval (Sum.elim (complexMatrixEntries z) (fun i => star (complexMatrixEntries z i)))
  change e (complexTotalEnergyPolynomial (fun ij : Fin m × Fin n => M ij.1 ij.2)^2) = _
  rw [map_pow,complexTotalEnergyPolynomial_eq_Gram_trace,AddMonoidHom.map_trace]
  congr 2
  ext i j
  exact eval_noncentralGramEntryPolynomial M z i j

theorem integral_actualNoncentralGram_trace_sq_closed {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) :
    (∫ z : ComplexSample (m := m) (n := n), ((complexGram (complexSampleMatrix z+M)).trace.re)^2
      ∂stdGaussian _) =
      (((m*n : ℕ) : ℝ)+∑ i, ∑ j, ‖M i j‖^2)^2 +
        ((m*n : ℕ) : ℝ)+2*(∑ i, ∑ j, ‖M i j‖^2) := by
  classical
  let P := complexTotalEnergyPolynomial (fun ij : Fin m × Fin n => M ij.1 ij.2)^2
  have hi := integrable_actualComplexMatrix_polynomial m n P
  have h := integral_actualComplexMatrix_polynomial m n P
  change _ = complexGaussianPolynomialMoment
    (complexTotalEnergyPolynomial (fun ij : Fin m × Fin n => M ij.1 ij.2)^2) at h
  rw [complexGaussianPolynomialMoment_total_energy_sq] at h
  have hm : (∑ ij : Fin m × Fin n, M ij.1 ij.2*star (M ij.1 ij.2)) =
      (complexGram M).trace := by
    rw [Fintype.sum_prod_type,Finset.sum_comm]
    simp only [complexGram,Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    simp only [RCLike.star_def]
    ring
  rw [hm] at h
  have he (z : ComplexSample (m := m) (n := n)) :
      (complexGaussianPolynomialEval P (complexMatrixEntries z)).re =
        ((complexGram (complexSampleMatrix z+M)).trace.re)^2 := by
    change (complexGaussianPolynomialEval
      (complexTotalEnergyPolynomial (fun ij : Fin m × Fin n => M ij.1 ij.2)^2) (complexMatrixEntries z)).re = _
    rw [eval_complexTotalEnergyPolynomial_sq]
    have hz := (RCLike.nonneg_iff.mp (complexGram_posSemidef (complexSampleMatrix z+M)).trace_nonneg).2
    change (complexGram (complexSampleMatrix z+M)).trace.im = 0 at hz
    simp [pow_two,Complex.mul_re,hz]
  have hr : (∫ z, (complexGaussianPolynomialEval P (complexMatrixEntries z)).re ∂stdGaussian _) =
      (∫ z, complexGaussianPolynomialEval P (complexMatrixEntries z) ∂stdGaussian _).re := by
    simpa using! integral_re hi
  simp_rw [he] at hr
  rw [hr,h]
  have hz := (RCLike.nonneg_iff.mp (complexGram_posSemidef M).trace_nonneg).2
  change (complexGram M).trace.im = 0 at hz
  norm_num [Fintype.card_prod,pow_two,Complex.add_re,Complex.mul_re,Complex.add_im,Complex.mul_im,hz]
  rw [complexGram_trace_re]
  push_cast
  ring

theorem integral_actualNoncentralGram_trace_centered_sq {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) :
    (∫ z : ComplexSample (m := m) (n := n),
      ((complexGram (complexSampleMatrix z+M)).trace.re-
        (((m*n : ℕ) : ℝ)+∑ i, ∑ j, ‖M i j‖^2))^2 ∂stdGaussian _) =
      ((m*n : ℕ) : ℝ)+2*(∑ i, ∑ j, ‖M i j‖^2) := by
  let T : ℝ := ((m*n : ℕ) : ℝ)+∑ i, ∑ j, ‖M i j‖^2
  have hi := integrable_actualNoncentralGram_trace M
  have hi2 := integrable_actualNoncentralGram_trace_sq M
  have he (z : ComplexSample (m := m) (n := n)) :
      ((complexGram (complexSampleMatrix z+M)).trace.re-T)^2 =
        ((complexGram (complexSampleMatrix z+M)).trace.re)^2-
          (2*T)*(complexGram (complexSampleMatrix z+M)).trace.re+T^2 := by ring
  change (∫ z, ((complexGram (complexSampleMatrix z+M)).trace.re-T)^2 ∂stdGaussian _) = _
  simp_rw [he]
  have ha := integral_add (hi2.sub (hi.const_mul (2*T))) (integrable_const (T^2))
  have hb := integral_sub hi2 (hi.const_mul (2*T))
  simp only [Pi.sub_apply,Pi.add_apply] at ha hb
  rw [ha,hb,integral_const_mul,integral_const]
  have hm : (∫ z : ComplexSample (m := m) (n := n),
      (complexGram (complexSampleMatrix z+M)).trace.re ∂stdGaussian _) = T :=
    actualExpectedGramPower_eq_closed M
  rw [integral_actualNoncentralGram_trace_sq_closed,hm]
  simp only [measureReal_def,measure_univ,ENNReal.toReal_one,one_smul]
  dsimp only [T]
  ring

end
end JinWishart
#print axioms JinWishart.complexTotalEnergyPolynomial_eq_Gram_trace
#print axioms JinWishart.eval_complexTotalEnergyPolynomial_sq
#print axioms JinWishart.integral_actualNoncentralGram_trace_sq_closed
#print axioms JinWishart.integral_actualNoncentralGram_trace_centered_sq
