import JinWishartFormalization.ComplexGaussianWeightedShiftedMoment
import JinWishartFormalization.CorrelatedGramMean

/-! General four-entry moments for ZB+M with fixed arbitrary rectangular B.
Codex. No inverse, rank, or target density assumption.
[需人工审查] Product Gaussian transport, variance and covariance orientation.
-/
open Matrix MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

def complexRowCoefficient {m p : ℕ} (k : Fin m) (a : Fin p → ℂ) :
    (Fin m × Fin p) → ℂ := fun t => if t.1=k then a t.2 else 0

theorem complexDirectLinearPolynomial_row {m p : ℕ} (k : Fin m) (a : Fin p → ℂ) :
    complexDirectLinearPolynomial (complexRowCoefficient k a) =
      ∑ b, MvPolynomial.C (a b)*MvPolynomial.X (Sum.inl (k,b)) := by
  classical
  simp [complexDirectLinearPolynomial,complexRowCoefficient,Fintype.sum_prod_type,apply_ite,ite_mul]

theorem complexConjugateLinearPolynomial_row {m p : ℕ} (k : Fin m) (a : Fin p → ℂ) :
    complexConjugateLinearPolynomial (complexRowCoefficient k a) =
      ∑ b, MvPolynomial.C (a b)*MvPolynomial.X (Sum.inr (k,b)) := by
  classical
  simp [complexConjugateLinearPolynomial,complexRowCoefficient,Fintype.sum_prod_type,apply_ite,ite_mul]

theorem complexRowCoefficient_pair {m p : ℕ} (k l : Fin m) (a c : Fin p → ℂ) :
    (∑ t, complexRowCoefficient k a t*complexRowCoefficient l c t) =
      if k=l then ∑ b, a b*c b else 0 := by
  classical
  by_cases h : k=l
  · subst l
    simp [complexRowCoefficient,Fintype.sum_prod_type,ite_mul,mul_ite]
  · simp [complexRowCoefficient,Fintype.sum_prod_type,ite_mul,mul_ite,h,Ne.symm h]

theorem complexRowCoefficient_gram {m p n : ℕ} (k l : Fin m)
    (B : Matrix (Fin p) (Fin n) ℂ) (i j : Fin n) :
    (∑ t, complexRowCoefficient k (fun b => B b j) t*
      complexRowCoefficient l (fun b => star (B b i)) t) =
      if k=l then complexGram B i j else 0 := by
  rw [complexRowCoefficient_pair]
  split_ifs <;> simp [complexGram,Matrix.mul_apply,Matrix.conjTranspose_apply,mul_comm]

def correlatedDirectEntryPolynomial {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (k : Fin m) (j : Fin n) :
    ComplexMatrixPolynomial m p :=
  complexDirectLinearPolynomial (complexRowCoefficient k (fun b => B b j))+MvPolynomial.C (M k j)

def correlatedConjugateEntryPolynomial {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (k : Fin m) (i : Fin n) :
    ComplexMatrixPolynomial m p :=
  complexConjugateLinearPolynomial (complexRowCoefficient k (fun b => star (B b i)))+
    MvPolynomial.C (star (M k i))

theorem eval_correlatedDirectEntryPolynomial {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (k : Fin m) (j : Fin n)
    (z : ComplexSample (m := m) (n := p)) :
    complexGaussianPolynomialEval (correlatedDirectEntryPolynomial B M k j) (complexMatrixEntries z) =
      (complexSampleMatrix z*B+M) k j := by
  simp [correlatedDirectEntryPolynomial,complexDirectLinearPolynomial_row,
    complexGaussianPolynomialEval,complexMatrixEntries,Matrix.mul_apply,Matrix.add_apply,mul_comm]

theorem eval_correlatedConjugateEntryPolynomial {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (k : Fin m) (i : Fin n)
    (z : ComplexSample (m := m) (n := p)) :
    complexGaussianPolynomialEval (correlatedConjugateEntryPolynomial B M k i) (complexMatrixEntries z) =
      star ((complexSampleMatrix z*B+M) k i) := by
  simp [correlatedConjugateEntryPolynomial,complexConjugateLinearPolynomial_row,
    complexGaussianPolynomialEval,complexMatrixEntries,Matrix.mul_apply,Matrix.add_apply,mul_comm]

set_option maxHeartbeats 1000000 in
theorem complexGaussianMoment_correlated_four_entry {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (k l : Fin m) (i j u v : Fin n) :
    complexGaussianPolynomialMoment
      (correlatedConjugateEntryPolynomial B M k i*correlatedDirectEntryPolynomial B M k j*
       correlatedConjugateEntryPolynomial B M l u*correlatedDirectEntryPolynomial B M l v) =
      star (M k i)*M k j*star (M l u)*M l v +
      complexGram B i j*star (M l u)*M l v + complexGram B u v*star (M k i)*M k j +
      (if k=l then 1 else 0)*(complexGram B i v*M k j*star (M l u)+
        complexGram B u j*star (M k i)*M l v) +
      complexGram B i j*complexGram B u v +
      (if k=l then 1 else 0)*complexGram B i v*complexGram B u j := by
  classical
  have h := complexGaussianPolynomialMoment_weighted_shifted_fourth
    (complexRowCoefficient k (fun b => B b j)) (complexRowCoefficient l (fun b => B b v))
    (complexRowCoefficient k (fun b => star (B b i)))
    (complexRowCoefficient l (fun b => star (B b u)))
    (M k j) (M l v) (star (M k i)) (star (M l u))
  simp only [complexRowCoefficient_gram,ite_true] at h
  change complexGaussianPolynomialMoment
    (correlatedDirectEntryPolynomial B M k j*correlatedDirectEntryPolynomial B M l v*
     correlatedConjugateEntryPolynomial B M k i*correlatedConjugateEntryPolynomial B M l u) = _ at h
  have he :
      correlatedConjugateEntryPolynomial B M k i*correlatedDirectEntryPolynomial B M k j*
        correlatedConjugateEntryPolynomial B M l u*correlatedDirectEntryPolynomial B M l v =
      correlatedDirectEntryPolynomial B M k j*correlatedDirectEntryPolynomial B M l v*
        correlatedConjugateEntryPolynomial B M k i*correlatedConjugateEntryPolynomial B M l u := by ring
  rw [he,h]
  by_cases hkl : k=l
  · subst l
    simp only [ite_true]
    ring
  · simp only [if_neg hkl,if_neg (Ne.symm hkl)]
    ring

theorem eval_correlatedFourEntryPolynomial {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (k l : Fin m) (i j u v : Fin n) (z : ComplexSample (m := m) (n := p)) :
    complexGaussianPolynomialEval
      (correlatedConjugateEntryPolynomial B M k i*correlatedDirectEntryPolynomial B M k j*
       correlatedConjugateEntryPolynomial B M l u*correlatedDirectEntryPolynomial B M l v)
      (complexMatrixEntries z) =
      star ((complexSampleMatrix z*B+M) k i)*(complexSampleMatrix z*B+M) k j*
      star ((complexSampleMatrix z*B+M) l u)*(complexSampleMatrix z*B+M) l v := by
  have hm (P Q : ComplexMatrixPolynomial m p) :
      complexGaussianPolynomialEval (P*Q) (complexMatrixEntries z) =
      complexGaussianPolynomialEval P (complexMatrixEntries z)*
        complexGaussianPolynomialEval Q (complexMatrixEntries z) := map_mul _ _ _
  simp only [hm,eval_correlatedDirectEntryPolynomial,eval_correlatedConjugateEntryPolynomial]

theorem integrable_actualCorrelated_four_entry {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (k l : Fin m) (i j u v : Fin n) :
    Integrable (fun z : ComplexSample (m := m) (n := p) =>
      star ((complexSampleMatrix z*B+M) k i)*(complexSampleMatrix z*B+M) k j*
      star ((complexSampleMatrix z*B+M) l u)*(complexSampleMatrix z*B+M) l v) (stdGaussian _) := by
  have h := integrable_actualComplexMatrix_polynomial m p
    (correlatedConjugateEntryPolynomial B M k i*correlatedDirectEntryPolynomial B M k j*
     correlatedConjugateEntryPolynomial B M l u*correlatedDirectEntryPolynomial B M l v)
  simpa only [eval_correlatedFourEntryPolynomial] using h

theorem integral_actualCorrelated_four_entry {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (k l : Fin m) (i j u v : Fin n) :
    (∫ z : ComplexSample (m := m) (n := p),
      star ((complexSampleMatrix z*B+M) k i)*(complexSampleMatrix z*B+M) k j*
      star ((complexSampleMatrix z*B+M) l u)*(complexSampleMatrix z*B+M) l v ∂stdGaussian _) =
      star (M k i)*M k j*star (M l u)*M l v +
      complexGram B i j*star (M l u)*M l v + complexGram B u v*star (M k i)*M k j +
      (if k=l then 1 else 0)*(complexGram B i v*M k j*star (M l u)+
        complexGram B u j*star (M k i)*M l v) +
      complexGram B i j*complexGram B u v +
      (if k=l then 1 else 0)*complexGram B i v*complexGram B u j := by
  have h := integral_actualComplexMatrix_polynomial m p
    (correlatedConjugateEntryPolynomial B M k i*correlatedDirectEntryPolynomial B M k j*
     correlatedConjugateEntryPolynomial B M l u*correlatedDirectEntryPolynomial B M l v)
  simp only [eval_correlatedFourEntryPolynomial,complexGaussianMoment_correlated_four_entry] at h
  exact h

end
end JinWishart
#print axioms JinWishart.complexDirectLinearPolynomial_row
#print axioms JinWishart.complexConjugateLinearPolynomial_row
#print axioms JinWishart.complexRowCoefficient_pair
#print axioms JinWishart.complexRowCoefficient_gram
#print axioms JinWishart.eval_correlatedDirectEntryPolynomial
#print axioms JinWishart.eval_correlatedConjugateEntryPolynomial
#print axioms JinWishart.complexGaussianMoment_correlated_four_entry
#print axioms JinWishart.integrable_actualCorrelated_four_entry
#print axioms JinWishart.integral_actualCorrelated_four_entry
#print axioms JinWishart.eval_correlatedFourEntryPolynomial
