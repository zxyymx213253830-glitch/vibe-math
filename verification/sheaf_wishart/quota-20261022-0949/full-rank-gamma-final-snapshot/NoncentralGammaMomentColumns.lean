import JinWishartFormalization.NoncentralFullRankNormalizer
import Mathlib.LinearAlgebra.Matrix.Block

/-! Codex. Seed2026102606 exact controls precede source.
Algebraic Gamma-column reduction for later partial-rank normalization.
No full Psi determinant evaluation, normalization integral or actual-law assertion.
[需人工审查] Row/column and source parameter conventions in later use. -/
open Polynomial Finset
namespace JinWishart
noncomputable section

theorem noncentralMomentPolynomial_coeff (q k j : ℕ) :
 (noncentralMomentPolynomial q k).coeff j =
   (k.factorial : ℝ)*((q+k).choose (q+j) : ℝ)/(j.factorial : ℝ) := by
 by_cases hj : j ≤ k
 · have hs : (q+k).choose (k-j) = (q+k).choose (q+j) :=
     Nat.choose_symm_of_eq_add (by omega)
   unfold noncentralMomentPolynomial
   simp only [finsetSum_coeff,coeff_C_mul_X_pow]
   rw [sum_eq_single j]
   · simp [hs]
   · intro b _ hb
     simp [Ne.symm hb]
   · intro hn
     exact (hn (mem_range.mpr (by omega))).elim
 · have hz : (noncentralMomentPolynomial q k).coeff j = 0 := by
     apply coeff_eq_zero_of_natDegree_lt
     rw [noncentralMomentPolynomial_natDegree]
     omega
   rw [hz,Nat.choose_eq_zero_of_lt (by omega)]
   simp

theorem noncentralMomentPolynomial_weighted_coeff (q k j : ℕ) :
 ((q+j).factorial : ℝ)*(noncentralMomentPolynomial q k).coeff j =
   ((q+k).factorial : ℝ)*(k.choose j : ℝ) := by
 rw [noncentralMomentPolynomial_coeff]
 by_cases hj : j ≤ k
 · have hc1 : ((q+k).choose (q+j) : ℝ)*((q+j).factorial : ℝ)*((k-j).factorial : ℝ) =
       ((q+k).factorial : ℝ) := by
     have h := Nat.choose_mul_factorial_mul_factorial (show q+j ≤ q+k by omega)
     rw [show q+k-(q+j)=k-j by omega] at h
     exact_mod_cast h
   have hc2 : (k.choose j : ℝ)*(j.factorial : ℝ)*((k-j).factorial : ℝ) =
       (k.factorial : ℝ) := by
     exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj
   have hj0 : (j.factorial : ℝ) ≠ 0 := by positivity
   have hk0 : ((k-j).factorial : ℝ) ≠ 0 := by positivity
   field_simp [hj0]
   apply mul_right_cancel₀ hk0
   linear_combination (k.factorial : ℝ)*hc1 - ((q+k).factorial : ℝ)*hc2
 · rw [Nat.choose_eq_zero_of_lt (show k<j by omega),
     Nat.choose_eq_zero_of_lt (show q+k<q+j by omega)]
   simp

theorem gammaMoment_column_eq_coefficient_sum (q k h : ℕ) :
 (∑ j ∈ range (h+1), (h.factorial : ℝ)*((q+h).choose (h-j) : ℝ)*
   ((q+j).factorial : ℝ)*(noncentralMomentPolynomial q k).coeff j) =
     ((q+k+h).factorial : ℝ) := by
 calc
  _ = (h.factorial : ℝ)*((q+k).factorial : ℝ)*
      ∑ j ∈ range (h+1), ((q+h).choose (h-j) : ℝ)*(k.choose j : ℝ) := by
    simp only [mul_sum]
    apply sum_congr rfl
    intro j _
    calc
     _ = (h.factorial : ℝ)*((q+h).choose (h-j) : ℝ)*
         (((q+j).factorial : ℝ)*(noncentralMomentPolynomial q k).coeff j) := by ring
     _ = _ := by rw [noncentralMomentPolynomial_weighted_coeff]; ring
  _ = ((q+k).factorial : ℝ)*
      (((k+q+h).factorial : ℝ)/((k+q).factorial : ℝ)) := by
    rw [factorial_ratio_vandermonde q h k]
    ring
  _ = _ := by
    rw [show q+k=k+q by omega]
    field_simp

def gammaMomentColumnTransform (q p : ℕ) : Matrix (Fin p) (Fin p) ℝ :=
 fun j h => if j.val ≤ h.val then
   (h.val.factorial : ℝ)*((q+h.val).choose (h.val-j.val) : ℝ)*((q+j.val).factorial : ℝ)
 else 0

theorem gammaMomentColumnTransform_det (q p : ℕ) :
 (gammaMomentColumnTransform q p).det =
   ∏ h : Fin p, (h.val.factorial : ℝ)*((q+h.val).factorial : ℝ) := by
 have ht : (gammaMomentColumnTransform q p).IsUpperTriangular := by
   intro i j hji
   simp only [gammaMomentColumnTransform]
   rw [ite_eq_right (show ¬ i.val ≤ j.val by exact not_le.mpr hji)]
 rw [Matrix.det_of_isUpperTriangular ht]
 apply Finset.prod_congr rfl
 intro h _
 simp [gammaMomentColumnTransform]

theorem gammaMomentColumnTransform_det_ne_zero (q p : ℕ) :
 (gammaMomentColumnTransform q p).det ≠ 0 := by
 rw [gammaMomentColumnTransform_det]
 apply Finset.prod_ne_zero_iff.mpr
 intro h _
 positivity

end
end JinWishart
#print axioms JinWishart.noncentralMomentPolynomial_coeff
#print axioms JinWishart.noncentralMomentPolynomial_weighted_coeff
#print axioms JinWishart.gammaMoment_column_eq_coefficient_sum
#print axioms JinWishart.gammaMomentColumnTransform_det
#print axioms JinWishart.gammaMomentColumnTransform_det_ne_zero
