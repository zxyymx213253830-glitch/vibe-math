import JinWishartFormalization.ComplexGaussianMomentFunctional

/-! Low-degree Gaussian factorial functional identities for a Wick expansion.
Codex. These are exact algebraic consequences of the existing moment functional,
not new independence assumptions. [需人工审查] Interpretation as actual moments.
-/
open scoped BigOperators
namespace JinWishart
noncomputable section

theorem complexGaussianPolynomialMoment_monomial {ι : Type*} [Fintype ι]
    (d : (ι ⊕ ι) →₀ ℕ) (c : ℂ) :
    complexGaussianPolynomialMoment (MvPolynomial.monomial d c) =
      c * ∏ i, if d (Sum.inl i)=d (Sum.inr i) then (Nat.factorial (d (Sum.inl i)) : ℂ) else 0 := by
  classical
  by_cases hc : c=0
  · simp [hc,complexGaussianPolynomialMoment]
  · simp [complexGaussianPolynomialMoment,MvPolynomial.support_monomial,hc]

theorem complexGaussianPolynomialMoment_X_conj_X {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι) :
    complexGaussianPolynomialMoment
      (MvPolynomial.X (Sum.inl a)*MvPolynomial.X (Sum.inr b) : MvPolynomial (ι ⊕ ι) ℂ) =
      if a=b then 1 else 0 := by
  classical
  simp only [MvPolynomial.X,MvPolynomial.monomial_mul_monomial,one_mul]
  rw [complexGaussianPolynomialMoment_monomial]
  simp only [one_mul,Finsupp.add_apply,Finsupp.single_apply,Sum.inl.injEq,Sum.inr.injEq,
    Sum.inl_ne_inr,Sum.inr_ne_inl,ite_false,zero_add,add_zero]
  by_cases hab : a=b
  · subst b
    simp only [ite_true]
    apply Finset.prod_eq_one
    intro i _
    split_ifs <;> norm_num
  · rw [if_neg hab]
    apply Finset.prod_eq_zero (Finset.mem_univ a)
    simp [hab,Ne.symm hab]

theorem complexGaussianPolynomialMoment_monomial_unbalanced {ι : Type*} [Fintype ι]
    (d : (ι ⊕ ι) →₀ ℕ) (c : ℂ)
    (hne : (∑ i, d (Sum.inl i)) ≠ ∑ i, d (Sum.inr i)) :
    complexGaussianPolynomialMoment (MvPolynomial.monomial d c) = 0 := by
  classical
  rw [complexGaussianPolynomialMoment_monomial]
  have hp : (∏ i, if d (Sum.inl i)=d (Sum.inr i)
      then (Nat.factorial (d (Sum.inl i)) : ℂ) else 0) = 0 := by
    by_contra hp
    apply hne
    apply Finset.sum_congr rfl
    intro i _
    by_contra hi
    exact hp (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]))
  rw [hp,mul_zero]

theorem complexGaussianPolynomialMoment_C {ι : Type*} [Fintype ι] (c : ℂ) :
    complexGaussianPolynomialMoment (MvPolynomial.C c : MvPolynomial (ι ⊕ ι) ℂ) = c := by
  change complexGaussianPolynomialMoment (MvPolynomial.monomial 0 c : MvPolynomial (ι ⊕ ι) ℂ) = c
  rw [complexGaussianPolynomialMoment_monomial]
  simp

theorem complexGaussianPolynomialMoment_X {ι : Type*} [Fintype ι] (a : ι ⊕ ι) :
    complexGaussianPolynomialMoment (MvPolynomial.X a : MvPolynomial (ι ⊕ ι) ℂ) = 0 := by
  classical
  simp only [MvPolynomial.X]
  apply complexGaussianPolynomialMoment_monomial_unbalanced
  rcases a with a | a <;> simp [Finsupp.single_apply]

theorem complexGaussianPolynomialMoment_direct_pair {ι : Type*} [Fintype ι] (a b : ι) :
    complexGaussianPolynomialMoment
      (MvPolynomial.X (Sum.inl a)*MvPolynomial.X (Sum.inl b) : MvPolynomial (ι ⊕ ι) ℂ) = 0 := by
  classical
  simp only [MvPolynomial.X,MvPolynomial.monomial_mul_monomial,one_mul]
  apply complexGaussianPolynomialMoment_monomial_unbalanced
  simp [Finsupp.add_apply,Finsupp.single_apply,Finset.sum_add_distrib]

theorem complexGaussianPolynomialMoment_conjugate_pair {ι : Type*} [Fintype ι] (a b : ι) :
    complexGaussianPolynomialMoment
      (MvPolynomial.X (Sum.inr a)*MvPolynomial.X (Sum.inr b) : MvPolynomial (ι ⊕ ι) ℂ) = 0 := by
  classical
  simp only [MvPolynomial.X,MvPolynomial.monomial_mul_monomial,one_mul]
  apply complexGaussianPolynomialMoment_monomial_unbalanced
  simp [Finsupp.add_apply,Finsupp.single_apply,Finset.sum_add_distrib]

theorem complexGaussianPolynomialMoment_direct_direct_conjugate {ι : Type*} [Fintype ι] (a b c : ι) :
    complexGaussianPolynomialMoment
      (MvPolynomial.X (Sum.inl a)*MvPolynomial.X (Sum.inl b)*MvPolynomial.X (Sum.inr c) :
        MvPolynomial (ι ⊕ ι) ℂ) = 0 := by
  classical
  simp only [MvPolynomial.X,MvPolynomial.monomial_mul_monomial,one_mul]
  apply complexGaussianPolynomialMoment_monomial_unbalanced
  simp [Finsupp.add_apply,Finsupp.single_apply,Finset.sum_add_distrib]

theorem complexGaussianPolynomialMoment_direct_conjugate_conjugate {ι : Type*} [Fintype ι] (a b c : ι) :
    complexGaussianPolynomialMoment
      (MvPolynomial.X (Sum.inl a)*MvPolynomial.X (Sum.inr b)*MvPolynomial.X (Sum.inr c) :
        MvPolynomial (ι ⊕ ι) ℂ) = 0 := by
  classical
  simp only [MvPolynomial.X,MvPolynomial.monomial_mul_monomial,one_mul]
  apply complexGaussianPolynomialMoment_monomial_unbalanced
  simp [Finsupp.add_apply,Finsupp.single_apply,Finset.sum_add_distrib]

theorem complexGaussianPolynomialMoment_fourth {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b c d : ι) :
    complexGaussianPolynomialMoment
      (MvPolynomial.X (Sum.inl a)*MvPolynomial.X (Sum.inl b)*
        MvPolynomial.X (Sum.inr c)*MvPolynomial.X (Sum.inr d) : MvPolynomial (ι ⊕ ι) ℂ) =
      (if a=c ∧ b=d then 1 else 0)+(if a=d ∧ b=c then 1 else 0) := by
  classical
  have hw (a b c d : ι) :
      complexGaussianPolynomialMoment
        (MvPolynomial.X (Sum.inl a)*MvPolynomial.X (Sum.inl b)*
          MvPolynomial.X (Sum.inr c)*MvPolynomial.X (Sum.inr d) : MvPolynomial (ι ⊕ ι) ℂ) =
        ∏ i, if (if a=i then 1 else 0)+(if b=i then 1 else 0) =
          ((if c=i then 1 else 0)+(if d=i then 1 else 0) : ℕ)
          then (Nat.factorial ((if a=i then 1 else 0)+(if b=i then 1 else 0)) : ℂ) else 0 := by
    simp only [MvPolynomial.X,MvPolynomial.monomial_mul_monomial,one_mul]
    rw [complexGaussianPolynomialMoment_monomial]
    simp only [one_mul,Finsupp.add_apply,Finsupp.single_apply,Sum.inl.injEq,Sum.inr.injEq,
      Sum.inl_ne_inr,Sum.inr_ne_inl,ite_false,zero_add,add_zero]
  have hm (a b : ι) : (∏ i : ι,
      (Nat.factorial ((if a=i then 1 else 0)+(if b=i then 1 else 0)) : ℂ)) =
      if a=b then 2 else 1 := by
    by_cases hab : a=b
    · subst b
      rw [if_pos rfl,Finset.prod_eq_single a]
      · norm_num
      · intro i _ hia
        simp [Ne.symm hia]
      · simp
    · rw [if_neg hab]
      apply Finset.prod_eq_one
      intro i _
      split_ifs <;> simp_all
  by_cases hp : (a=c ∧ b=d) ∨ (a=d ∧ b=c)
  · rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · rw [hw]
      simp only [ite_true]
      rw [hm]
      by_cases hab : a=b
      · subst b; norm_num
      · simp [hab,Ne.symm hab]
    · rw [hw]
      have he (i : ι) :
          (if a=i then 1 else 0)+(if b=i then 1 else 0) =
            ((if b=i then 1 else 0)+(if a=i then 1 else 0) : ℕ) := Nat.add_comm _ _
      simp only [he,ite_true]
      rw [hm]
      by_cases hab : a=b
      · subst b; norm_num
      · simp [hab,Ne.symm hab]
  · have h1 : ¬(a=c ∧ b=d) := fun h => hp (Or.inl h)
    have h2 : ¬(a=d ∧ b=c) := fun h => hp (Or.inr h)
    rw [if_neg h1,if_neg h2,add_zero,hw]
    by_contra hne
    have hc (i : ι) : (if a=i then 1 else 0)+(if b=i then 1 else 0) =
        ((if c=i then 1 else 0)+(if d=i then 1 else 0) : ℕ) := by
      by_contra hi
      exact hne (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]))
    apply hp
    by_cases hab : a=b
    · subst b
      have ha := hc a
      by_cases hca : c=a
      · by_cases hda : d=a
        · exact Or.inl ⟨hca.symm,hda.symm⟩
        · simp [hca,hda] at ha
      · by_cases hda : d=a
        · simp [hca,hda] at ha
        · simp [hca,hda] at ha
    · by_cases hac : a=c
      · subst c
        have hb := hc b
        by_cases hbd : b=d
        · exact Or.inl ⟨rfl,hbd⟩
        · simp [hab,Ne.symm hab,Ne.symm hbd] at hb
      · have ha := hc a
        by_cases had : a=d
        · subst d
          have hb := hc b
          by_cases hbc : b=c
          · exact Or.inr ⟨rfl,hbc⟩
          · simp [hab,Ne.symm hab,Ne.symm hbc] at hb
        · simp [hab,hac,had,Ne.symm hab,Ne.symm hac,Ne.symm had] at ha

end
end JinWishart
#print axioms JinWishart.complexGaussianPolynomialMoment_monomial
#print axioms JinWishart.complexGaussianPolynomialMoment_X_conj_X
#print axioms JinWishart.complexGaussianPolynomialMoment_monomial_unbalanced
#print axioms JinWishart.complexGaussianPolynomialMoment_C
#print axioms JinWishart.complexGaussianPolynomialMoment_X
#print axioms JinWishart.complexGaussianPolynomialMoment_direct_pair
#print axioms JinWishart.complexGaussianPolynomialMoment_conjugate_pair
#print axioms JinWishart.complexGaussianPolynomialMoment_direct_direct_conjugate
#print axioms JinWishart.complexGaussianPolynomialMoment_direct_conjugate_conjugate
#print axioms JinWishart.complexGaussianPolynomialMoment_fourth
