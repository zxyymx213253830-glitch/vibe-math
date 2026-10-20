import JinWishartFormalization.CorrelatedGaussianFourthMoment

/-! General Gram-entry covariance (without conjugating the second entry).
Codex. Fixed rectangular/singular factors allowed. Exact controls before proof.
[需人工审查] Actual Gaussian moment transport and covariance conventions.
-/
open Matrix MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

theorem correlatedGramEntryPolynomial_eq_sum {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (i j : Fin n) :
    correlatedGramEntryPolynomial B M i j =
      ∑ k, correlatedConjugateEntryPolynomial B M k i*correlatedDirectEntryPolynomial B M k j := by
  simp [correlatedGramEntryPolynomial,correlatedConjugateEntryPolynomial,
    correlatedDirectEntryPolynomial,complexConjugateLinearPolynomial_row,
    complexDirectLinearPolynomial_row,mul_comm]

set_option maxHeartbeats 1000000 in
theorem complexGaussianMoment_correlatedGramEntry_product {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (i j u v : Fin n) :
    complexGaussianPolynomialMoment
      (correlatedGramEntryPolynomial B M i j*correlatedGramEntryPolynomial B M u v) =
      ((m : ℂ)*complexGram B i j+complexGram M i j)*
        ((m : ℂ)*complexGram B u v+complexGram M u v) +
      (m : ℂ)*complexGram B i v*complexGram B u j +
      complexGram B i v*complexGram M u j+complexGram B u j*complexGram M i v := by
  classical
  let S := complexGram B
  let A := complexGram M
  have hm (i j : Fin n) : (∑ k, star (M k i)*M k j) = A i j := by
    simp [A,complexGram,Matrix.mul_apply,Matrix.conjTranspose_apply]
  have hL (P : ComplexMatrixPolynomial m p) :
      complexGaussianMomentLinear P = complexGaussianPolynomialMoment P := rfl
  have hs : complexGaussianPolynomialMoment
      (correlatedGramEntryPolynomial B M i j*correlatedGramEntryPolynomial B M u v) =
      ∑ k, ∑ l, (star (M k i)*M k j*star (M l u)*M l v +
      S i j*star (M l u)*M l v + S u v*star (M k i)*M k j +
      (if k=l then 1 else 0)*(S i v*M k j*star (M l u)+S u j*star (M k i)*M l v) +
      S i j*S u v+(if k=l then 1 else 0)*S i v*S u j) := by
    change complexGaussianMomentLinear _ = _
    rw [correlatedGramEntryPolynomial_eq_sum,correlatedGramEntryPolynomial_eq_sum,Finset.sum_mul]
    simp only [Finset.mul_sum,map_sum]
    simp only [hL]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    simpa only [mul_assoc] using complexGaussianMoment_correlated_four_entry B M k l i j u v
  rw [hs]
  simp only [Finset.sum_add_distrib]
  have hmean : (∑ k, ∑ l, star (M k i)*M k j*star (M l u)*M l v) = A i j*A u v := by
    have he (k l : Fin m) : star (M k i)*M k j*star (M l u)*M l v =
        (star (M k i)*M k j)*(star (M l u)*M l v) := by ring
    simp only [he,← Finset.mul_sum,← Finset.sum_mul,hm]
  have hfirst : (∑ k : Fin m, ∑ l, S i j*star (M l u)*M l v) = (m : ℂ)*S i j*A u v := by
    have he (l : Fin m) : S i j*star (M l u)*M l v = S i j*(star (M l u)*M l v) := by ring
    simp only [he,← Finset.mul_sum,hm,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    ring
  have hsecond : (∑ k, ∑ l : Fin m, S u v*star (M k i)*M k j) = (m : ℂ)*S u v*A i j := by
    have he (k : Fin m) : S u v*star (M k i)*M k j = S u v*(star (M k i)*M k j) := by ring
    simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      ← Finset.mul_sum,hm]
    ring
  have hcross : (∑ k, ∑ l, (if k=l then (1 : ℂ) else 0)*
      (S i v*M k j*star (M l u)+S u j*star (M k i)*M l v)) = S i v*A u j+S u j*A i v := by
    simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    have he (k : Fin m) : S i v*M k j*star (M k u)+S u j*star (M k i)*M k v =
        S i v*(star (M k u)*M k j)+S u j*(star (M k i)*M k v) := by ring
    simp only [he,Finset.sum_add_distrib,← Finset.mul_sum,hm]
  have hnoise : (∑ _k : Fin m, ∑ _l : Fin m, S i j*S u v) =
      (m : ℂ)^2*S i j*S u v := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    ring
  have hdiag : (∑ k : Fin m, ∑ l : Fin m, (if k=l then (1 : ℂ) else 0)*S i v*S u j) =
      (m : ℂ)*S i v*S u j := by
    simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
      Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    ring
  rw [hmean,hfirst,hsecond,hcross,hnoise,hdiag]
  change _ = ((m : ℂ)*S i j+A i j)*((m : ℂ)*S u v+A u v)+
    (m : ℂ)*S i v*S u j+S i v*A u j+S u j*A i v
  ring

theorem eval_correlatedGramEntry_product {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (i j u v : Fin n)
    (z : ComplexSample (m := m) (n := p)) :
    complexGaussianPolynomialEval
      (correlatedGramEntryPolynomial B M i j*correlatedGramEntryPolynomial B M u v)
      (complexMatrixEntries z) =
      complexGram (complexSampleMatrix z*B+M) i j*complexGram (complexSampleMatrix z*B+M) u v := by
  have hm (P Q : ComplexMatrixPolynomial m p) :
      complexGaussianPolynomialEval (P*Q) (complexMatrixEntries z) =
      complexGaussianPolynomialEval P (complexMatrixEntries z)*
        complexGaussianPolynomialEval Q (complexMatrixEntries z) := map_mul _ _ _
  simp only [hm,eval_correlatedGramEntryPolynomial]

theorem integrable_actualCorrelatedGram_entry_product {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (i j u v : Fin n) :
    Integrable (fun z : ComplexSample (m := m) (n := p) =>
      complexGram (complexSampleMatrix z*B+M) i j*complexGram (complexSampleMatrix z*B+M) u v)
      (stdGaussian _) := by
  have h := integrable_actualComplexMatrix_polynomial m p
    (correlatedGramEntryPolynomial B M i j*correlatedGramEntryPolynomial B M u v)
  simpa only [eval_correlatedGramEntry_product] using h

theorem integral_actualCorrelatedGram_entry_product {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (i j u v : Fin n) :
    (∫ z : ComplexSample (m := m) (n := p),
      complexGram (complexSampleMatrix z*B+M) i j*complexGram (complexSampleMatrix z*B+M) u v ∂stdGaussian _) =
      ((m : ℂ)*complexGram B i j+complexGram M i j)*
        ((m : ℂ)*complexGram B u v+complexGram M u v) +
      (m : ℂ)*complexGram B i v*complexGram B u j +
      complexGram B i v*complexGram M u j+complexGram B u j*complexGram M i v := by
  have h := integral_actualComplexMatrix_polynomial m p
    (correlatedGramEntryPolynomial B M i j*correlatedGramEntryPolynomial B M u v)
  simpa only [eval_correlatedGramEntry_product,complexGaussianMoment_correlatedGramEntry_product] using h

end
end JinWishart
#print axioms JinWishart.correlatedGramEntryPolynomial_eq_sum
#print axioms JinWishart.complexGaussianMoment_correlatedGramEntry_product
#print axioms JinWishart.eval_correlatedGramEntry_product
#print axioms JinWishart.integrable_actualCorrelatedGram_entry_product
#print axioms JinWishart.integral_actualCorrelatedGram_entry_product
