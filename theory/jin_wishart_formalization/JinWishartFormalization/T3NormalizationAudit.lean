import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Theorem 3 normalization audit

This isolated module formalizes only the explicit real constants in the paper's
Eq. (47), Eq. (24), and the common column factors read from Eq. (60). It makes
no claim about the probability integral or about the correctness of the paper's
probability theorem.

The result records the residual inactive-column factorial factor. -/

open Finset

namespace JinWishart.T3NormalizationAudit

noncomputable section

/-- The normalized multivariate factorial `Γ_n(r) = ∏_{i=1}^n (r-i)!`. -/
def factorialMultigamma (n r : ℕ) : ℝ :=
  ∏ i : Fin n, (Nat.factorial (r - (i.val + 1)) : ℝ)

/-- The active-eigenvalue Vandermonde factor appearing in the paper. -/
def activeVandermonde {L : ℕ} (lambda : Fin L → ℝ) : ℝ :=
  ∏ i : Fin L,
    ∏ j ∈ (Finset.univ : Finset (Fin L)).filter (fun j => i < j),
      (lambda i - lambda j)

/-- The paper's `c₁` in Eq. (47), with `tr Ω = ∑ lambda_i`. -/
def paperC1 (s t L : ℕ) (lambda : Fin L → ℝ) : ℝ :=
  Real.exp (-(∑ i : Fin L, lambda i)) *
    (((Nat.factorial (t - s) : ℝ) ^ s)⁻¹) /
    (factorialMultigamma (s - L) (s - L) *
      (∏ i : Fin L, Real.rpow (lambda i) (s - L : ℝ)) *
      activeVandermonde lambda)

/-- Column factor in Eq. (60) for one of the `L` active columns. -/
def activeColumnFactor (s t : ℕ) {L : ℕ} (lambda : Fin L → ℝ)
    (i : Fin L) : ℝ :=
  (Nat.factorial (t - s) : ℝ) *
    Real.rpow (lambda i) (((s : ℝ) - t) / 2) * Real.exp (lambda i)

/-- Column factor in Eq. (60) for an inactive column. The index `i : Fin (s-L)`
corresponds to the paper's one-based column `j=L+i+1`. -/
def inactiveColumnFactor (s t L : ℕ) (i : Fin (s - L)) : ℝ :=
  (Nat.factorial (t - s) : ℝ) /
    (Nat.factorial (t - L - (i.val + 1)) : ℝ)

/-- Product of all column factors, split into active and inactive columns. -/
def paperColumnFactorProduct (s t L : ℕ) (lambda : Fin L → ℝ) : ℝ :=
  (∏ i : Fin L, activeColumnFactor s t lambda i) *
    (∏ i : Fin (s - L), inactiveColumnFactor s t L i)

/-- The paper's displayed `c₃` in Eq. (24), with its Gamma factor in the
denominator. -/
def paperC3 (s t L : ℕ) (lambda : Fin L → ℝ) : ℝ :=
  (∏ i : Fin L,
      Real.rpow (lambda i) ((2 * (L : ℝ) - s - t) / 2)) /
    (factorialMultigamma (s - L) (s - L) * activeVandermonde lambda)

private theorem factorialMultigamma_pos (n r : ℕ) :
    0 < factorialMultigamma n r := by
  unfold factorialMultigamma
  apply Finset.prod_pos
  intro i hi
  exact Nat.cast_pos.mpr (Nat.factorial_pos (r - (i.val + 1)))

private theorem inactiveFactorProduct_eq (s t L : ℕ) (hst : s ≤ t)
    (hLs : L ≤ s) :
    (∏ i : Fin (s - L), inactiveColumnFactor s t L i) =
      (Nat.factorial (t - s) : ℝ) ^ (s - L) /
        factorialMultigamma (s - L) (t - L) := by
  unfold inactiveColumnFactor factorialMultigamma
  rw [Finset.prod_div_distrib]
  simp [Finset.prod_const]

private theorem activeFactorProduct_eq (s t L : ℕ) (lambda : Fin L → ℝ) :
    (∏ i : Fin L, activeColumnFactor s t lambda i) =
      (Nat.factorial (t - s) : ℝ) ^ L *
        (∏ i : Fin L, Real.rpow (lambda i) (((s : ℝ) - t) / 2)) *
        Real.exp (∑ i : Fin L, lambda i) := by
  unfold activeColumnFactor
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Real.exp_sum]

private theorem activePowerProduct_identity (s t L : ℕ)
    (lambda : Fin L → ℝ) (hPos : ∀ i, 0 < lambda i) :
    (∏ i : Fin L,
        Real.rpow (lambda i) ((2 * (L : ℝ) - s - t) / 2)) *
      (∏ i : Fin L, Real.rpow (lambda i) (s - L : ℝ)) =
      ∏ i : Fin L, Real.rpow (lambda i) (((s : ℝ) - t) / 2) := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  have hExp :
      ((2 * (L : ℝ) - s - t) / 2) + (s - L : ℝ) = ((s : ℝ) - t) / 2 := by
    ring
  calc
    _ = Real.rpow (lambda i)
        (((2 * (L : ℝ) - s - t) / 2) + (s - L : ℝ)) :=
          (Real.rpow_add (hPos i) _ _).symm
    _ = _ := by rw [hExp]

/-- Exact conversion of the displayed `c₁` times all Eq. (60) column factors:
the inactive columns leave `Γ_{s-L}(t-L)` in the denominator. This is an
algebraic identity only; no integration or probability statement is used. -/
theorem paperC1_mul_columnFactors_eq_paperC3_div_inactiveGamma
    (s t L : ℕ) (hst : s ≤ t) (hLs : L ≤ s)
    (lambda : Fin L → ℝ) (hPos : ∀ i, 0 < lambda i)
    (hDistinct : ∀ i j, i < j → lambda i ≠ lambda j) :
    paperC1 s t L lambda * paperColumnFactorProduct s t L lambda =
      paperC3 s t L lambda / factorialMultigamma (s - L) (t - L) := by
  have hV : activeVandermonde lambda ≠ 0 := by
    unfold activeVandermonde
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact sub_ne_zero.mpr (hDistinct i j (Finset.mem_filter.mp hj).2)
  have hFac : 0 < (Nat.factorial (t - s) : ℝ) := by
    exact Nat.cast_pos.mpr (Nat.factorial_pos (t - s))
  have hGamma0 : factorialMultigamma (s - L) (s - L) ≠ 0 :=
    (factorialMultigamma_pos (s - L) (s - L)).ne'
  have hGamma1 : factorialMultigamma (s - L) (t - L) ≠ 0 :=
    (factorialMultigamma_pos (s - L) (t - L)).ne'
  have hPow : (∏ i : Fin L,
      Real.rpow (lambda i) (s - L : ℝ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact (Real.rpow_pos_of_pos (hPos i) _).ne'
  have hFacPow :
      (Nat.factorial (t - s) : ℝ) ^ L *
          (Nat.factorial (t - s) : ℝ) ^ (s - L) =
        (Nat.factorial (t - s) : ℝ) ^ s := by
    rw [← pow_add]
    congr 1
    exact Nat.add_sub_of_le hLs
  have hExp :
      Real.exp (-(∑ i : Fin L, lambda i)) *
          Real.exp (∑ i : Fin L, lambda i) = 1 := by
    rw [← Real.exp_add]
    rw [neg_add_cancel]
    simp
  have hScale :
      Real.exp (-(∑ i : Fin L, lambda i)) *
          ((Nat.factorial (t - s) : ℝ) ^ L *
            Real.exp (∑ i : Fin L, lambda i) *
              (Nat.factorial (t - s) : ℝ) ^ (s - L)) =
        (Nat.factorial (t - s) : ℝ) ^ s := by
    calc
      _ = (Real.exp (-(∑ i : Fin L, lambda i)) *
            Real.exp (∑ i : Fin L, lambda i)) *
          ((Nat.factorial (t - s) : ℝ) ^ L *
            (Nat.factorial (t - s) : ℝ) ^ (s - L)) := by ring
      _ = 1 * (Nat.factorial (t - s) : ℝ) ^ s := by rw [hExp, hFacPow]
      _ = _ := by ring
  have hScaleTarget :
      Real.exp (-(∑ i : Fin L, lambda i)) *
          (Nat.factorial (t - s) : ℝ) ^ L *
          (Nat.factorial (t - s) : ℝ) ^ (s - L) *
          Real.exp (∑ i : Fin L, lambda i) =
        (Nat.factorial (t - s) : ℝ) ^ s := by
    calc
      _ = (Real.exp (-(∑ i : Fin L, lambda i)) *
            Real.exp (∑ i : Fin L, lambda i)) *
          ((Nat.factorial (t - s) : ℝ) ^ L *
            (Nat.factorial (t - s) : ℝ) ^ (s - L)) := by ring
      _ = 1 * (Nat.factorial (t - s) : ℝ) ^ s := by rw [hExp, hFacPow]
      _ = _ := by ring
  have hScaleA :
      (Real.exp (-(∑ i : Fin L, lambda i)) *
        (Nat.factorial (t - s) : ℝ) ^ L *
        (Nat.factorial (t - s) : ℝ) ^ (s - L) *
        (∏ i : Fin L, Real.rpow (lambda i) ((2 * (L : ℝ) - s - t) / 2))) *
        Real.exp (∑ i : Fin L, lambda i) =
      (Nat.factorial (t - s) : ℝ) ^ s *
        (∏ i : Fin L, Real.rpow (lambda i) ((2 * (L : ℝ) - s - t) / 2)) := by
    calc
      _ = (Real.exp (-(∑ i : Fin L, lambda i)) *
          (Nat.factorial (t - s) : ℝ) ^ L *
          (Nat.factorial (t - s) : ℝ) ^ (s - L) *
          Real.exp (∑ i : Fin L, lambda i)) *
          (∏ i : Fin L, Real.rpow (lambda i) ((2 * (L : ℝ) - s - t) / 2)) := by ring
      _ = _ := by rw [hScaleTarget]
  have hScaleB :
      Real.exp (-(∑ i : Fin L, lambda i)) *
        (Nat.factorial (t - s) : ℝ) ^ L *
        (Nat.factorial (t - s) : ℝ) ^ (s - L) *
        Real.exp (∑ i : Fin L, lambda i) *
        (∏ i : Fin L, Real.rpow (lambda i) ((2 * (L : ℝ) - s - t) / 2)) =
      (Nat.factorial (t - s) : ℝ) ^ s *
        (∏ i : Fin L, Real.rpow (lambda i) ((2 * (L : ℝ) - s - t) / 2)) := by
    calc
      _ = (Real.exp (-(∑ i : Fin L, lambda i)) *
          (Nat.factorial (t - s) : ℝ) ^ L *
          (Nat.factorial (t - s) : ℝ) ^ (s - L) *
          Real.exp (∑ i : Fin L, lambda i)) *
          (∏ i : Fin L, Real.rpow (lambda i) ((2 * (L : ℝ) - s - t) / 2)) := by ring
      _ = _ := by rw [hScaleTarget]
  have hActive := activeFactorProduct_eq s t L lambda
  have hInactive := inactiveFactorProduct_eq s t L hst hLs
  have hPowers := activePowerProduct_identity s t L lambda hPos
  unfold paperC1 paperColumnFactorProduct paperC3
  rw [hActive, hInactive]
  rw [← hPowers]
  field_simp [hFac.ne', hGamma0, hGamma1, hV, hPow]
  have hScaleFinal :
      (Real.exp (-(∑ i : Fin L, lambda i)) *
          (Nat.factorial (t - s) : ℝ) ^ L *
          (∏ i : Fin L, Real.rpow (lambda i) (((L : ℝ) * 2 - s - t) / 2))) *
          Real.exp (∑ i : Fin L, lambda i) *
          (Nat.factorial (t - s) : ℝ) ^ (s - L) =
        (Nat.factorial (t - s) : ℝ) ^ s *
          (∏ i : Fin L, Real.rpow (lambda i) (((L : ℝ) * 2 - s - t) / 2)) := by
    calc
      _ = (Real.exp (-(∑ i : Fin L, lambda i)) *
            (Nat.factorial (t - s) : ℝ) ^ L *
            (Nat.factorial (t - s) : ℝ) ^ (s - L) *
            Real.exp (∑ i : Fin L, lambda i)) *
            (∏ i : Fin L, Real.rpow (lambda i) (((L : ℝ) * 2 - s - t) / 2)) := by ring
      _ = _ := by rw [hScaleTarget]
  exact hScaleFinal

/-- For `s=3,t=4,L=1`, the inactive Gamma factor is `Γ₂(3)=2`, so its
reciprocal is exactly `1/2`. -/
theorem residualInactiveFactor_s3_t4_L1 :
    (factorialMultigamma (3 - 1) (4 - 1))⁻¹ = (1 / 2 : ℝ) := by
  rw [factorialMultigamma, Fin.prod_univ_two]
  norm_num

end

end JinWishart.T3NormalizationAudit
