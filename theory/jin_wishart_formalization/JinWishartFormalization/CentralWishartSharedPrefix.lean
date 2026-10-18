import JinWishartFormalization.CentralWishartSharedPivot
import JinWishartFormalization.GaussianDisjointPrincipalLaw

/-!
# Iterating shared-column peeling and closing disjoint residual moments

Codex proof bodies. Arbitrary common-prefix length and disjoint residual selectors.
[需人工审查] Actual joint law and source-column interpretation; no density premise.
-/
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace JinWishart
noncomputable section

def centralSharedPrefixSelection {k n : ℕ} (c : ℕ) (e : Fin k → Fin n) :
    Fin (k+c) → Fin (n+c) :=
  match c with
  | 0 => e
  | c+1 => centralPivotSelection (centralSharedPrefixSelection c e)

theorem centralDeterminantPowerMoment_succ (d n p : ℕ) :
    centralDeterminantPowerMoment d (n+1) p = centralDeterminantPowerMoment d n p *
      (((Nat.factorial (d+n+p) : ℕ) : ℝ) / ((Nat.factorial (d+n) : ℕ) : ℝ)) := by
  simp only [centralDeterminantPowerMoment, Fin.prod_univ_castSucc,
    Fin.val_castSucc, Fin.val_last]

theorem complexWishart_shared_prefix_moment (m n c k l p q : ℕ)
    (e : Fin k → Fin n) (f : Fin l → Fin n) :
    (∫⁻ A, ENNReal.ofReal (‖(A.submatrix (centralSharedPrefixSelection c e)
          (centralSharedPrefixSelection c e)).det‖^p) *
        ENNReal.ofReal (‖(A.submatrix (centralSharedPrefixSelection c f)
          (centralSharedPrefixSelection c f)).det‖^q)
      ∂complexWishart (m := m+c) (n := n+c)) =
      ENNReal.ofReal (centralDeterminantPowerMoment m c (p+q)) *
        ∫⁻ B, ENNReal.ofReal (‖(B.submatrix e e).det‖^p) *
          ENNReal.ofReal (‖(B.submatrix f f).det‖^q)
          ∂complexWishart (m := m) (n := n) := by
  induction c with
  | zero => simp [centralSharedPrefixSelection, centralDeterminantPowerMoment]
  | succ c ih =>
      change (∫⁻ A, ENNReal.ofReal (‖(A.submatrix
          (centralPivotSelection (centralSharedPrefixSelection c e))
          (centralPivotSelection (centralSharedPrefixSelection c e))).det‖^p) *
        ENNReal.ofReal (‖(A.submatrix
          (centralPivotSelection (centralSharedPrefixSelection c f))
          (centralPivotSelection (centralSharedPrefixSelection c f))).det‖^q)
        ∂complexWishart (m := (m+c)+1) (n := (n+c)+1)) = _
      rw [complexWishart_shared_pivot_moment, ih,
        centralDeterminantPowerMoment_succ,
        ENNReal.ofReal_mul (centralDeterminantPowerMoment_pos m c (p+q)).le]
      simp only [Nat.add_assoc]
      ring

/-- Closed mixed moments with c common initial columns and disjoint exclusive selectors.
The minors are generally dependent; all shared Gamma powers are retained. -/
theorem complexWishart_common_prefix_disjoint_moment (m n c k l p q : ℕ)
    (e : Fin k → Fin n) (f : Fin l → Fin n)
    (h : Function.Injective (Sum.elim e f)) (hk : k ≤ m) (hl : l ≤ m) :
    (∫⁻ A, ENNReal.ofReal (‖(A.submatrix (centralSharedPrefixSelection c e)
          (centralSharedPrefixSelection c e)).det‖^p) *
        ENNReal.ofReal (‖(A.submatrix (centralSharedPrefixSelection c f)
          (centralSharedPrefixSelection c f)).det‖^q)
      ∂complexWishart (m := m+c) (n := n+c)) =
      ENNReal.ofReal (centralDeterminantPowerMoment m c (p+q)) *
        (ENNReal.ofReal (centralDeterminantPowerMoment (m-k) k p) *
          ENNReal.ofReal (centralDeterminantPowerMoment (m-l) l q)) := by
  rw [complexWishart_shared_prefix_moment,
    complexWishart_disjoint_determinant_moment m n k l p q e f h hk hl]

end
end JinWishart
#print axioms JinWishart.centralDeterminantPowerMoment_succ
#print axioms JinWishart.complexWishart_shared_prefix_moment
#print axioms JinWishart.complexWishart_common_prefix_disjoint_moment
