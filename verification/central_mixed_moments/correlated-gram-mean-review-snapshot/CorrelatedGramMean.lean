import JinWishartFormalization.ComplexGaussianWickMoments
import JinWishartFormalization.NoncentralGramPolynomialMoments

/-! Actual expected Gram entry for a fixed arbitrary rectangular/singular factor B.
Codex. No inverse, target density, or invertibility assumption.
[需人工审查] Correlated covariance/model and Gaussian polynomial transport.
-/
open Matrix MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

def correlatedGramEntryPolynomial {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (i j : Fin n) : ComplexMatrixPolynomial m p :=
  ∑ k, ((∑ a, MvPolynomial.X (Sum.inr (k,a))*MvPolynomial.C (star (B a i)))+
      MvPolynomial.C (star (M k i))) *
    ((∑ b, MvPolynomial.X (Sum.inl (k,b))*MvPolynomial.C (B b j))+
      MvPolynomial.C (M k j))

theorem complexGaussianMoment_correlated_row_pair {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (k : Fin m) (i j : Fin n) :
    complexGaussianPolynomialMoment
      ((((∑ a, MvPolynomial.X (Sum.inr (k,a))*MvPolynomial.C (star (B a i)))+
        MvPolynomial.C (star (M k i))) *
       ((∑ b, MvPolynomial.X (Sum.inl (k,b))*MvPolynomial.C (B b j))+
        MvPolynomial.C (M k j))) : ComplexMatrixPolynomial m p) =
      (∑ a, star (B a i)*B a j)+star (M k i)*M k j := by
  classical
  have he : ((((∑ a, MvPolynomial.X (Sum.inr (k,a))*MvPolynomial.C (star (B a i)))+
        MvPolynomial.C (star (M k i))) *
       ((∑ b, MvPolynomial.X (Sum.inl (k,b))*MvPolynomial.C (B b j))+
        MvPolynomial.C (M k j))) : ComplexMatrixPolynomial m p) =
      (∑ a, ∑ b, (star (B a i)*B b j) •
        (MvPolynomial.X (Sum.inl (k,b))*MvPolynomial.X (Sum.inr (k,a)))) +
      (∑ a, (star (B a i)*M k j) • MvPolynomial.X (Sum.inr (k,a))) +
      (∑ b, (star (M k i)*B b j) • MvPolynomial.X (Sum.inl (k,b))) +
      MvPolynomial.C (star (M k i)*M k j) := by
    have hd : ((∑ a, MvPolynomial.X (Sum.inr (k,a))*MvPolynomial.C (star (B a i))) *
        (∑ b, MvPolynomial.X (Sum.inl (k,b))*MvPolynomial.C (B b j)) : ComplexMatrixPolynomial m p) =
        ∑ a, ∑ b, (star (B a i)*B b j) •
          (MvPolynomial.X (Sum.inl (k,b))*MvPolynomial.X (Sum.inr (k,a))) := by
      simp only [Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      simp only [MvPolynomial.smul_eq_C_mul,map_mul]
      ring
    have ha : ((∑ a, MvPolynomial.X (Sum.inr (k,a))*MvPolynomial.C (star (B a i))) *
        MvPolynomial.C (M k j) : ComplexMatrixPolynomial m p) =
        ∑ a, (star (B a i)*M k j) • MvPolynomial.X (Sum.inr (k,a)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      simp only [MvPolynomial.smul_eq_C_mul,map_mul]
      ring
    have hb : (MvPolynomial.C (star (M k i)) *
        (∑ b, MvPolynomial.X (Sum.inl (k,b))*MvPolynomial.C (B b j)) : ComplexMatrixPolynomial m p) =
        ∑ b, (star (M k i)*B b j) • MvPolynomial.X (Sum.inl (k,b)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      simp only [MvPolynomial.smul_eq_C_mul,map_mul]
      ring
    rw [add_mul,mul_add,mul_add,hd,ha,hb,← map_mul]
    ring
  have hL (P : ComplexMatrixPolynomial m p) :
      complexGaussianMomentLinear P = complexGaussianPolynomialMoment P := rfl
  change complexGaussianMomentLinear _ = _
  rw [he]
  simp only [map_add,map_sum,map_smul]
  simp only [hL,complexGaussianPolynomialMoment_X_conj_X,complexGaussianPolynomialMoment_X,
    complexGaussianPolynomialMoment_C,Prod.mk.injEq,true_and,smul_eq_mul,mul_zero,
    Finset.sum_const_zero,add_zero,zero_add]
  simp

theorem complexGaussianMoment_correlatedGramEntryPolynomial {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (i j : Fin n) :
    complexGaussianPolynomialMoment (correlatedGramEntryPolynomial B M i j) =
      (m : ℂ)*(complexGram B) i j+(complexGram M) i j := by
  classical
  change complexGaussianMomentLinear _ = _
  simp only [correlatedGramEntryPolynomial,map_sum]
  change (∑ k, complexGaussianPolynomialMoment _) = _
  simp_rw [complexGaussianMoment_correlated_row_pair]
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    complexGram,Matrix.mul_apply,Matrix.conjTranspose_apply,RCLike.star_def]

theorem eval_correlatedGramEntryPolynomial {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (i j : Fin n)
    (z : ComplexSample (m := m) (n := p)) :
    complexGaussianPolynomialEval (correlatedGramEntryPolynomial B M i j) (complexMatrixEntries z) =
      complexGram (complexSampleMatrix z*B+M) i j := by
  classical
  simp [complexGaussianPolynomialEval,correlatedGramEntryPolynomial,complexMatrixEntries,
    complexGram,Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.add_apply,map_sum,map_add,map_mul,mul_comm]

theorem integrable_actualCorrelatedGram_entry {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (i j : Fin n) :
    Integrable (fun z : ComplexSample (m := m) (n := p) =>
      complexGram (complexSampleMatrix z*B+M) i j) (stdGaussian _) := by
  have h := integrable_actualComplexMatrix_polynomial m p (correlatedGramEntryPolynomial B M i j)
  simp_rw [eval_correlatedGramEntryPolynomial] at h
  exact h

theorem integral_actualCorrelatedGram_entry {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (i j : Fin n) :
    (∫ z : ComplexSample (m := m) (n := p), complexGram (complexSampleMatrix z*B+M) i j ∂stdGaussian _) =
      (m : ℂ)*(complexGram B) i j+(complexGram M) i j := by
  have h := integral_actualComplexMatrix_polynomial m p (correlatedGramEntryPolynomial B M i j)
  simp_rw [eval_correlatedGramEntryPolynomial] at h
  rw [complexGaussianMoment_correlatedGramEntryPolynomial] at h
  exact h

end
end JinWishart
#print axioms JinWishart.complexGaussianMoment_correlated_row_pair
#print axioms JinWishart.complexGaussianMoment_correlatedGramEntryPolynomial
#print axioms JinWishart.eval_correlatedGramEntryPolynomial
#print axioms JinWishart.integrable_actualCorrelatedGram_entry
#print axioms JinWishart.integral_actualCorrelatedGram_entry
