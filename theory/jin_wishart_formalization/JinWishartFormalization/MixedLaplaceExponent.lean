import JinWishartFormalization.ScaledMixedMomentMatrix
import Mathlib.Algebra.BigOperators.Intervals

/-! Codex. Seed 2026103012 exact integer controls precede source. Finite
scaling exponent algebra only. [需人工审查] Eventual matrix/model mapping. -/
open Finset
namespace JinWishart
noncomputable section

def triangularIndexSum (n : ℕ) : ℕ := ∑ i : Fin n, i.val

theorem triangularIndexSum_double (n : ℕ) :
 2*triangularIndexSum n+n = n*n := by
 cases n with
 | zero => simp [triangularIndexSum]
 | succ n =>
   have h := Finset.sum_range_id_mul_two (n+1)
   simp only [Nat.add_sub_cancel] at h
   have ht : triangularIndexSum (n+1) = ∑ i ∈ Finset.range (n+1), i := by
     exact Fin.sum_univ_eq_sum_range (fun i : ℕ => i) (n+1)
   rw [ht]
   nlinarith

theorem mixedLaplaceExponent_identity (p L q : ℕ) :
 (∑ i : Fin (p+L), (q+i.val+1)) +
 (∑ a : Fin p, a.val) + L*p + (∑ j : Fin L, j.val) = (p+L)*(p+L+q) := by
 have hsum : (∑ i : Fin (p+L), (q+i.val+1)) =
     (p+L)*(q+1)+triangularIndexSum (p+L) := by
   simp only [Finset.sum_add_distrib,Finset.sum_const_zero,Finset.sum_const,
     Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,triangularIndexSum]
   simp only [Nat.cast_add,Nat.cast_id]
   ring
 rw [hsum]
 change (p+L)*(q+1)+triangularIndexSum (p+L)+triangularIndexSum p+L*p+
   triangularIndexSum L = (p+L)*(p+L+q)
 have h := triangularIndexSum_double (p+L)
 have hp := triangularIndexSum_double p
 have hL := triangularIndexSum_double L
 nlinarith

theorem vandermonde_det_div_scale (L : ℕ) (lambda : Fin L → ℝ) (c : ℝ) :
 (Matrix.vandermonde (fun i => lambda i/c)).det =
 (∏ j : Fin L, (c^j.val)⁻¹) * (Matrix.vandermonde lambda).det := by
 have h : Matrix.vandermonde (fun i => lambda i/c) =
     Matrix.of (fun i j => (c^j.val)⁻¹ * Matrix.vandermonde lambda i j) := by
   ext i j
   simp [Matrix.vandermonde,div_eq_mul_inv,mul_pow,inv_pow,mul_comm]
 rw [h,Matrix.det_mul_row]

theorem mixedNoncentralMomentMatrix_det_div_scale (p L q : ℕ) (lambda : Fin L → ℝ) (c : ℝ) :
 (mixedNoncentralMomentMatrix q p L (fun b => lambda b/c)).det =
 (∏ j : Fin L, (c^(p+j.val))⁻¹) * (mixedNoncentralMomentMatrix q p L lambda).det := by
 rw [mixedNoncentralMomentMatrix_det,mixedNoncentralMomentMatrix_det,
   vandermonde_det_div_scale]
 simp only [div_eq_mul_inv,mul_pow,Finset.prod_mul_distrib,pow_add,mul_inv_rev]
 ring

theorem mixedLaplace_power_product (p L q : ℕ) (c : ℝ) :
 (∏ i : Fin (p+L), (c^(q+i.val+1))⁻¹) *
 (∏ a : Fin p, (c^a.val)⁻¹) *
 (∏ j : Fin L, (c^(p+j.val))⁻¹) = (c^((p+L)*(p+L+q)))⁻¹ := by
 simp only [← inv_pow,Finset.prod_pow_eq_pow_sum,← pow_add]
 have hs : (∑ j : Fin L, (p + (j : ℕ))) = L*p + (∑ j : Fin L, (j : ℕ)) := by
   simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
 rw [hs]
 rw [← add_assoc,mixedLaplaceExponent_identity]

end
end JinWishart
#print axioms JinWishart.triangularIndexSum_double
#print axioms JinWishart.mixedLaplaceExponent_identity
#print axioms JinWishart.vandermonde_det_div_scale
#print axioms JinWishart.mixedNoncentralMomentMatrix_det_div_scale
#print axioms JinWishart.mixedLaplace_power_product
