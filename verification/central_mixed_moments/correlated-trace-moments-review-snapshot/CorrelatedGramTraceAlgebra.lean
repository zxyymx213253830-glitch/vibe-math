import JinWishartFormalization.CorrelatedGramEntryCovariance

/-! Finite functional trace moments for arbitrary fixed covariance factors.
Codex algebra. trace(W^2) is distinct from (trace W)^2.
[需人工审查] Actual Gaussian interpretation is transported separately.
-/
open Matrix
namespace JinWishart
noncomputable section

def correlatedGramTracePolynomial {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) : ComplexMatrixPolynomial m p :=
  ∑ i, correlatedGramEntryPolynomial B M i i

def correlatedGramSquaredTracePolynomial {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) : ComplexMatrixPolynomial m p :=
  ∑ i, ∑ j, correlatedGramEntryPolynomial B M i j*correlatedGramEntryPolynomial B M j i

theorem complexGaussianMoment_correlatedGram_trace {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) :
    complexGaussianPolynomialMoment (correlatedGramTracePolynomial B M) =
      ((m : ℂ) • complexGram B+complexGram M).trace := by
  change complexGaussianMomentLinear _ = _
  simp only [correlatedGramTracePolynomial,map_sum]
  change (∑ i, complexGaussianPolynomialMoment _) = _
  simp only [complexGaussianMoment_correlatedGramEntryPolynomial,Matrix.trace,Matrix.diag,
    Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]

set_option maxHeartbeats 1000000 in
theorem complexGaussianMoment_correlatedGram_squaredTrace {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) :
    complexGaussianPolynomialMoment (correlatedGramSquaredTracePolynomial B M) =
      (((m : ℂ) • complexGram B+complexGram M)^2).trace +
      (m : ℂ)*(complexGram B).trace^2+2*(complexGram B).trace*(complexGram M).trace := by
  classical
  let S := complexGram B
  let A := complexGram M
  let K := (m : ℂ) • S+A
  have hL (P : ComplexMatrixPolynomial m p) :
      complexGaussianMomentLinear P = complexGaussianPolynomialMoment P := rfl
  change complexGaussianMomentLinear _ = _
  simp only [correlatedGramSquaredTracePolynomial,map_sum]
  simp only [hL,complexGaussianMoment_correlatedGramEntry_product]
  change (∑ i, ∑ j, (K i j*K j i+(m : ℂ)*S i i*S j j+S i i*A j j+S j j*A i i)) =
    (K^2).trace+(m : ℂ)*S.trace^2+2*S.trace*A.trace
  simp only [Finset.sum_add_distrib]
  have hs (U V : Matrix (Fin n) (Fin n) ℂ) :
      (∑ i, ∑ j, U i i*V j j) = U.trace*V.trace := by
    simp only [← Finset.mul_sum,← Finset.sum_mul,Matrix.trace,Matrix.diag]
  have hmean : (∑ i, ∑ j, K i j*K j i) = (K^2).trace := by
    simp only [pow_two,Matrix.trace,Matrix.diag,Matrix.mul_apply]
  have hnoise : (∑ i, ∑ j, (m : ℂ)*S i i*S j j) = (m : ℂ)*S.trace^2 := by
    calc
      _ = (m : ℂ)*(∑ i, ∑ j, S i i*S j j) := by simp only [Finset.mul_sum,mul_assoc]
      _ = _ := by rw [hs,pow_two]
  have hswap : (∑ i, ∑ j, S j j*A i i) = ∑ i, ∑ j, S i i*A j j := Finset.sum_comm
  rw [hmean,hnoise,hs,hswap,hs]
  ring

set_option maxHeartbeats 1000000 in
theorem complexGaussianMoment_correlatedGram_trace_sq {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) :
    complexGaussianPolynomialMoment ((correlatedGramTracePolynomial B M)^2) =
      (((m : ℂ) • complexGram B+complexGram M).trace)^2 +
      (m : ℂ)*((complexGram B)^2).trace+2*(complexGram B*complexGram M).trace := by
  classical
  let S := complexGram B
  let A := complexGram M
  let K := (m : ℂ) • S+A
  have hL (P : ComplexMatrixPolynomial m p) :
      complexGaussianMomentLinear P = complexGaussianPolynomialMoment P := rfl
  change complexGaussianMomentLinear _ = _
  simp only [correlatedGramTracePolynomial,pow_two,Finset.sum_mul,Finset.mul_sum,map_sum]
  simp only [hL,complexGaussianMoment_correlatedGramEntry_product]
  simp only [← pow_two]
  change (∑ j, ∑ i, (K i i*K j j+(m : ℂ)*S i j*S j i+S i j*A j i+S j i*A i j)) =
    K.trace^2+(m : ℂ)*(S^2).trace+2*(S*A).trace
  rw [Finset.sum_comm]
  simp only [Finset.sum_add_distrib]
  have hmean : (∑ i, ∑ j, K i i*K j j) = K.trace^2 := by
    simp only [← Finset.mul_sum,← Finset.sum_mul,Matrix.trace,Matrix.diag,pow_two]
  have hnoise : (∑ i, ∑ j, (m : ℂ)*S i j*S j i) = (m : ℂ)*(S^2).trace := by
    simp only [pow_two,Matrix.trace,Matrix.diag,Matrix.mul_apply,Finset.mul_sum,mul_assoc]
  have hc : (∑ i, ∑ j, S i j*A j i) = (S*A).trace := by
    simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply]
  have hd : (∑ i, ∑ j, S j i*A i j) = (S*A).trace := by
    rw [Finset.sum_comm]
    simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply]
  rw [hmean,hnoise,hc,hd]
  ring

end
end JinWishart
#print axioms JinWishart.complexGaussianMoment_correlatedGram_trace
#print axioms JinWishart.complexGaussianMoment_correlatedGram_squaredTrace
#print axioms JinWishart.complexGaussianMoment_correlatedGram_trace_sq
