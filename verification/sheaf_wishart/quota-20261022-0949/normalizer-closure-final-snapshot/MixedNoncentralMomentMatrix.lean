import JinWishartFormalization.NoncentralGammaMomentColumns
import JinWishartFormalization.ZeroConfluentVandermonde
import Mathlib.Logic.Equiv.Fin.Basic

/-! Codex. Seed2026102608 exact factorization controls precede source.
Ascending monic moment rows, central coefficient/Gamma columns first.
This is not yet the original Psi Fin-index assembly or an actual joint law.
[需人工审查] Fin/Sum assembly and eventual source/model normalization. -/
open Polynomial Matrix Finset
namespace JinWishart
noncomputable section

def mixedMomentDegree (p L : ℕ) (i : Fin p ⊕ Fin L) : ℕ :=
 (finSumFinEquiv (m := p) (n := L) i).val

def mixedMomentCoefficientBasis (q p L : ℕ) :
 Matrix (Fin p ⊕ Fin L) (Fin p ⊕ Fin L) ℝ :=
 Matrix.of (fun i j => (noncentralMomentPolynomial q (mixedMomentDegree p L i)).coeff
   (mixedMomentDegree p L j))

def mixedMomentEvaluationBasis (q p L : ℕ) (lambda : Fin L → ℝ) :
 Matrix (Fin p ⊕ Fin L) (Fin p ⊕ Fin L) ℝ :=
 Matrix.of (fun i j => match j with
 | Sum.inl h => (noncentralMomentPolynomial q (mixedMomentDegree p L i)).coeff h.val
 | Sum.inr j => poissonFactorialMomentPolynomial q (mixedMomentDegree p L i) (lambda j))

def mixedNoncentralMomentMatrix (q p L : ℕ) (lambda : Fin L → ℝ) :
 Matrix (Fin p ⊕ Fin L) (Fin p ⊕ Fin L) ℝ :=
 Matrix.of (fun i j => match j with
 | Sum.inl h => ((q+mixedMomentDegree p L i+h.val).factorial : ℝ)
 | Sum.inr j => poissonFactorialMomentPolynomial q (mixedMomentDegree p L i) (lambda j))

def mixedGammaColumnBlock (q p L : ℕ) :
 Matrix (Fin p ⊕ Fin L) (Fin p ⊕ Fin L) ℝ :=
 Matrix.fromBlocks (gammaMomentColumnTransform q p) 0 0 1

theorem gammaMomentColumnTransform_coeff_sum (q k p : ℕ) (h : Fin p) :
 (∑ j : Fin p, (noncentralMomentPolynomial q k).coeff j.val *
   gammaMomentColumnTransform q p j h) = ((q+k+h.val).factorial : ℝ) := by
 let f : ℕ → ℝ := fun j => (noncentralMomentPolynomial q k).coeff j *
   (if j ≤ h.val then (h.val.factorial : ℝ)*((q+h.val).choose (h.val-j) : ℝ)*
     ((q+j).factorial : ℝ) else 0)
 change (∑ j : Fin p, f j.val) = _
 rw [Fin.sum_univ_eq_sum_range]
 have hsub : range (h.val+1) ⊆ range p := by
   intro j hj
   simp only [mem_range] at hj ⊢
   omega
 calc
  _ = ∑ j ∈ range (h.val+1), f j := by
    symm
    apply sum_subset hsub
    intro j hj hn
    have hjh : ¬ j ≤ h.val := by
      simp only [mem_range] at hn
      omega
    simp [f,hjh]
  _ = ∑ j ∈ range (h.val+1), (h.val.factorial : ℝ)*
      ((q+h.val).choose (h.val-j) : ℝ)*((q+j).factorial : ℝ)*
        (noncentralMomentPolynomial q k).coeff j := by
    apply sum_congr rfl
    intro j hj
    have hjh : j ≤ h.val := by simpa using (Nat.le_of_lt_succ (mem_range.mp hj))
    simp only [f,ite_eq_left hjh]
    ring
  _ = _ := gammaMoment_column_eq_coefficient_sum q k h.val

theorem mixedMomentCoefficientBasis_det (q p L : ℕ) :
 (mixedMomentCoefficientBasis q p L).det = 1 := by
 let A : Matrix (Fin (p+L)) (Fin (p+L)) ℝ := Matrix.of
   (fun i j => (noncentralMomentPolynomial q i.val).coeff j.val)
 have hA : A.det = 1 := by
   have ht := Matrix.det_matrixOfPolynomials
     (fun i : Fin (p+L) => noncentralMomentPolynomial q i.val)
     (fun i => noncentralMomentPolynomial_natDegree q i.val)
     (fun i => noncentralMomentPolynomial_monic q i.val)
   change (Matrix.of (fun i j : Fin (p+L) =>
     (noncentralMomentPolynomial q j.val).coeff i.val)).transpose.det = 1
   rw [Matrix.det_transpose]
   exact ht
 have he : mixedMomentCoefficientBasis q p L =
   A.submatrix (finSumFinEquiv (m := p) (n := L)) finSumFinEquiv := rfl
 rw [he,Matrix.det_submatrix_equiv_self,hA]

private theorem coefficient_mul_confluent (q p L : ℕ) (lambda : Fin L → ℝ) :
 mixedMomentCoefficientBasis q p L * zeroConfluentVandermonde p L lambda =
   mixedMomentEvaluationBasis q p L lambda := by
 ext i j
 cases j with
 | inl h =>
   simp [Matrix.mul_apply,Fintype.sum_sum_type,mixedMomentCoefficientBasis,
     zeroConfluentVandermonde,Matrix.fromBlocks,Matrix.one_apply,mixedMomentEvaluationBasis,mixedMomentDegree]
 | inr j =>
   have hd : (noncentralMomentPolynomial q (mixedMomentDegree p L i)).natDegree < p+L := by
     rw [noncentralMomentPolynomial_natDegree]
     exact (finSumFinEquiv i).isLt
   have hs := Equiv.sum_comp (finSumFinEquiv (m := p) (n := L))
     (fun r : Fin (p+L) =>
       (noncentralMomentPolynomial q (mixedMomentDegree p L i)).coeff r.val * lambda j^r.val)
   have hv : poissonFactorialMomentPolynomial q (mixedMomentDegree p L i) (lambda j) =
       ∑ r : Fin (p+L),
         (noncentralMomentPolynomial q (mixedMomentDegree p L i)).coeff r.val * lambda j^r.val := by
     rw [← noncentralMomentPolynomial_eval,Polynomial.eval_eq_sum_range' hd,
       ← Fin.sum_univ_eq_sum_range]
   change _ = poissonFactorialMomentPolynomial q (mixedMomentDegree p L i) (lambda j)
   rw [hv]
   simpa [Matrix.mul_apply,Fintype.sum_sum_type,mixedMomentCoefficientBasis,
     zeroConfluentVandermonde,Matrix.fromBlocks,Matrix.one_apply,mixedMomentEvaluationBasis,mixedMomentDegree] using hs

private theorem evaluation_mul_gamma (q p L : ℕ) (lambda : Fin L → ℝ) :
 mixedMomentEvaluationBasis q p L lambda * mixedGammaColumnBlock q p L =
   mixedNoncentralMomentMatrix q p L lambda := by
 ext i j
 cases j with
 | inl h =>
   simpa [Matrix.mul_apply,Fintype.sum_sum_type,mixedMomentEvaluationBasis,
     mixedGammaColumnBlock,Matrix.fromBlocks,Matrix.one_apply,mixedNoncentralMomentMatrix] using
       gammaMomentColumnTransform_coeff_sum q (mixedMomentDegree p L i) p h
 | inr j =>
   simp [Matrix.mul_apply,Fintype.sum_sum_type,mixedMomentEvaluationBasis,
     mixedGammaColumnBlock,Matrix.fromBlocks,Matrix.one_apply,mixedNoncentralMomentMatrix]

theorem mixedNoncentralMomentMatrix_factorization (q p L : ℕ) (lambda : Fin L → ℝ) :
 mixedNoncentralMomentMatrix q p L lambda =
   mixedMomentCoefficientBasis q p L * zeroConfluentVandermonde p L lambda *
     mixedGammaColumnBlock q p L := by
 rw [coefficient_mul_confluent,evaluation_mul_gamma]

theorem mixedNoncentralMomentMatrix_det (q p L : ℕ) (lambda : Fin L → ℝ) :
 (mixedNoncentralMomentMatrix q p L lambda).det =
   ((∏ j : Fin L, lambda j ^ p)*(Matrix.vandermonde lambda).det)*
     (∏ h : Fin p, (h.val.factorial : ℝ)*((q+h.val).factorial : ℝ)) := by
 rw [mixedNoncentralMomentMatrix_factorization,Matrix.det_mul,Matrix.det_mul,
   mixedMomentCoefficientBasis_det,one_mul,zeroConfluentVandermonde_det]
 simp only [mixedGammaColumnBlock,Matrix.det_fromBlocks_zero₂₁,Matrix.det_one,mul_one,
   gammaMomentColumnTransform_det]

theorem mixedNoncentralMomentMatrix_det_ne_zero (q p L : ℕ) (lambda : Fin L → ℝ)
 (hnz : ∀ j, lambda j ≠ 0) (hinj : Function.Injective lambda) :
 (mixedNoncentralMomentMatrix q p L lambda).det ≠ 0 := by
 rw [mixedNoncentralMomentMatrix_det]
 apply mul_ne_zero
   (mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun j _ => pow_ne_zero p (hnz j)))
     (Matrix.det_vandermonde_ne_zero_iff.mpr hinj))
 apply Finset.prod_ne_zero_iff.mpr
 intro h _
 positivity

end
end JinWishart
#print axioms JinWishart.gammaMomentColumnTransform_coeff_sum
#print axioms JinWishart.mixedMomentCoefficientBasis_det
#print axioms JinWishart.mixedNoncentralMomentMatrix_factorization
#print axioms JinWishart.mixedNoncentralMomentMatrix_det
#print axioms JinWishart.mixedNoncentralMomentMatrix_det_ne_zero
