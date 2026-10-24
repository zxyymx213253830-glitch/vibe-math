import JinWishartFormalization.OneSurplusGammaHankel

/-! Codex. Seed2026102403 controls before source.
Original central T1 in all positive sizes with exactly one extra row.
[需人工审查] Original formula indexing, raw Gram convention and inherited CDF. -/
open Matrix MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

theorem theorem1CentralOneSurplus_PsiDet (n : ℕ) (x : ℝ) (hx : 0≤x) :
    (theorem1PsiMatrix n (n+1) 0 (by omega) (Nat.zero_le n)
      (fun j : Fin 0 => Fin.elim0 j) x).det =
      (Real.exp (-(n : ℝ)*x) : ℂ)*
      (∏ i : Fin n,(i.val.factorial : ℂ)*((i.val+1).factorial : ℂ))*
      (oneExtraRowMinimumPolynomial n x : ℂ) := by
  have heq : theorem1PsiMatrix n (n+1) 0 (by omega) (Nat.zero_le n)
      (fun j : Fin 0 => Fin.elim0 j) x=
      Matrix.reindex (Fin.revPerm : Fin n ≃ Fin n) Fin.revPerm
        (Matrix.of (fun i j : Fin n => upperGammaNat (i.val+j.val+1) x)) := by
    ext i j
    simp only [theorem1PsiMatrix,theorem1PsiEntry,Nat.not_lt_zero,↓reduceDIte,
      Matrix.reindex_apply,Matrix.of_apply,Fin.revPerm_symm,Fin.revPerm_apply]
    congr 1
    change n+(n+1)-(i.val+1)-(j.val+1)=(n-(i.val+1))+(n-(j.val+1))+1
    omega
  rw [heq,Matrix.det_reindex_self]
  exact upperGammaHankel_one_surplus_det n x hx

theorem theorem1CentralOneSurplus_candidate_eq_polynomial (n : ℕ) (x : ℝ) (hx : 0≤x) :
    theorem1CdfCandidate n (n+1) 0 (by omega) (Nat.zero_le n)
      (fun j : Fin 0 => Fin.elim0 j) x =
      1-Real.exp (-(n : ℝ)*x)*oneExtraRowMinimumPolynomial n x := by
  have hD : (∏ i : Fin n,(i.val.factorial : ℂ)*((i.val+1).factorial : ℂ))≠0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero i.val)
      (by exact_mod_cast Nat.factorial_ne_zero (i.val+1))
  have hDN := norm_ne_zero_iff.mpr hD
  have hP0 : oneExtraRowMinimumPolynomial n 0=1 := by simp [oneExtraRowMinimumPolynomial]
  rw [theorem1CdfCandidate,theorem1CentralOneSurplus_PsiDet n x hx,
    theorem1CentralOneSurplus_PsiDet n 0 (by norm_num),hP0]
  simp only [mul_zero,neg_zero,Real.exp_zero,Complex.ofReal_one,one_mul,mul_one]
  rw [norm_mul,norm_mul,Complex.norm_of_nonneg (Real.exp_nonneg _),
    Complex.norm_of_nonneg (oneExtraRowMinimumPolynomial_nonneg n x hx)]
  field_simp
  <;> ring

theorem theorem1CentralOneSurplus_candidate_eq_actualCDF (n : ℕ) (hn : 0<n)
    (x : ℝ) (hx : 0≤x) :
    theorem1CdfCandidate n (n+1) 0 (by omega) (Nat.zero_le n)
      (fun j : Fin 0 => Fin.elim0 j) x =
      ((stdGaussian (ComplexSample (m := n+1) (n := n)))
        {z | oneExtraRowSampleMinimum n hn z≤x}).toReal := by
  rw [theorem1CentralOneSurplus_candidate_eq_polynomial n x hx,
    actualOneExtraRow_minimum_CDF n hn x hx]

end
end JinWishart
#print axioms JinWishart.theorem1CentralOneSurplus_PsiDet
#print axioms JinWishart.theorem1CentralOneSurplus_candidate_eq_polynomial
#print axioms JinWishart.theorem1CentralOneSurplus_candidate_eq_actualCDF
