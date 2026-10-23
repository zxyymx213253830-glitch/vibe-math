import JinWishartFormalization.Theorem1CentralSquare
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.Polynomial.Pochhammer

/-! Central rectangular Gamma determinant normalization, no CDF premise.
Codex. Seed2026102247:324 exact controls before source. Reuses pinned
Vandermonde and monic rising-factorial polynomial results.
[需人工审查] Original-paper indexing/normalization interpretation only;
these deterministic equalities do not identify a rectangular probability law. -/
open Matrix Polynomial
namespace JinWishart
noncomputable section

private theorem consecutiveVandermonde_det (n : ℕ) :
    (Matrix.vandermonde (fun i : Fin n => (i.val : ℂ))).det=
      ∏ i : Fin n,(i.val.factorial : ℂ) := by
  cases n with
  | zero => simp
  | succ n =>
    rw [Matrix.det_vandermonde_id_eq_superFactorial]
    rw [Fin.prod_univ_eq_prod_range (fun i : ℕ => (i.factorial : ℂ)) (n+1),
      ← Nat.cast_prod,Nat.prod_range_succ_factorial]

theorem factorialHankel_offset_det (n d : ℕ) :
    Matrix.det (fun i j : Fin n => ((d+i.val+j.val).factorial : ℂ))=
      ∏ i : Fin n,(i.val.factorial : ℂ)*((d+i.val).factorial : ℂ) := by
  classical
  let v : Fin n → ℂ := fun i => (i.val : ℂ)+((d : ℂ)+1)
  let E : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.of (fun i j => (ascPochhammer ℂ j.val).eval (v i))
  have hE : E.det=∏ i : Fin n,(i.val.factorial : ℂ) := by
    have he := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde v
      (fun j : Fin n => ascPochhammer ℂ j.val)
      (fun j => ascPochhammer_natDegree ℂ j.val)
      (fun j => monic_ascPochhammer ℂ j.val)
    change (Matrix.vandermonde v).det=E.det at he
    rw [← he]
    dsimp only [v]
    rw [Matrix.det_vandermonde_add,consecutiveVandermonde_det]
  have hmat : Matrix.of (fun i j : Fin n => ((d+i.val+j.val).factorial : ℂ))=
      Matrix.of (fun i j : Fin n => ((d+j.val).factorial : ℂ)*E.transpose i j) := by
    ext i j
    change ((d+i.val+j.val).factorial : ℂ)=
      ((d+j.val).factorial : ℂ)*(ascPochhammer ℂ i.val).eval ((j.val : ℂ)+((d : ℂ)+1))
    calc
      _=((d+j.val+i.val).factorial : ℂ) :=
        congrArg (fun k : ℕ => (k.factorial : ℂ)) (by omega)
      _=((d+j.val).factorial : ℂ)*(ascPochhammer ℂ i.val).eval (((d+j.val : ℕ) : ℂ)+1) :=
        (factorial_mul_ascPochhammer ℂ (d+j.val) i.val).symm
      _=_ := by congr 2;push_cast;ring
  change (Matrix.of (fun i j : Fin n => ((d+i.val+j.val).factorial : ℂ))).det=_
  rw [hmat,Matrix.det_mul_row,Matrix.det_transpose,hE,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  ring

theorem theorem1Central_PsiDet_zero (s t : ℕ) (hst : s≤t) :
    (theorem1PsiMatrix s t 0 hst (Nat.zero_le s)
      (fun j : Fin 0 => Fin.elim0 j) 0).det=
      ∏ i : Fin s,(i.val.factorial : ℂ)*((t-s+i.val).factorial : ℂ) := by
  have heq : theorem1PsiMatrix s t 0 hst (Nat.zero_le s)
      (fun j : Fin 0 => Fin.elim0 j) 0=
      Matrix.reindex (Fin.revPerm : Fin s ≃ Fin s) Fin.revPerm
        (Matrix.of (fun i j : Fin s => ((t-s+i.val+j.val).factorial : ℂ))) := by
    ext i j
    simp only [theorem1PsiMatrix,theorem1PsiEntry,Nat.not_lt_zero,↓reduceDIte,
      Matrix.reindex_apply,Matrix.of_apply,Fin.revPerm_symm,Fin.revPerm_apply]
    change upperGammaNat (theorem1GammaIndex s t i j) 0=
      ((t-s+(s-(i.val+1))+(s-(j.val+1))).factorial : ℂ)
    have hidx : theorem1GammaIndex s t i j=t-s+(s-(i.val+1))+(s-(j.val+1)) := by
      unfold theorem1GammaIndex
      omega
    rw [upperGammaNat_at_zero_eq_factorial,hidx]
  rw [heq,Matrix.det_reindex_self]
  exact factorialHankel_offset_det s (t-s)

theorem theorem1Central_PsiDet_zero_norm_pos (s t : ℕ) (hst : s≤t) :
    0<‖(theorem1PsiMatrix s t 0 hst (Nat.zero_le s)
      (fun j : Fin 0 => Fin.elim0 j) 0).det‖ := by
  rw [theorem1Central_PsiDet_zero]
  apply norm_pos_iff.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero i.val)
    (by exact_mod_cast Nat.factorial_ne_zero (t-s+i.val))

end
end JinWishart
#print axioms JinWishart.factorialHankel_offset_det
#print axioms JinWishart.theorem1Central_PsiDet_zero
#print axioms JinWishart.theorem1Central_PsiDet_zero_norm_pos
