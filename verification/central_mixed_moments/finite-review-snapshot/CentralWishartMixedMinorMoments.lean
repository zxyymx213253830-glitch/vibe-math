import JinWishartFormalization.FiniteMinorOverlapModel

/-!
# Actual mixed moments of ANY two principal minors

Codex proof bodies. All common/exclusive reindexing is constructed in Lean.
[需人工审查] Actual Bartlett law and nonnegative moment interpretation.
-/
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal ComplexOrder
namespace JinWishart
noncomputable section

def centralMixedMinorMoment (t : ℕ) {n : ℕ} (S T : Finset (Fin n)) (p q : ℕ) : ℝ :=
  centralDeterminantPowerMoment (t-(S ∩ T).card) (S ∩ T).card (p+q) *
    (centralDeterminantPowerMoment (t-(S ∩ T).card-(S \ T).card) (S \ T).card p *
      centralDeterminantPowerMoment (t-(S ∩ T).card-(T \ S).card) (T \ S).card q)

theorem centralMixedMinorMoment_pos (t : ℕ) {n : ℕ}
    (S T : Finset (Fin n)) (p q : ℕ) : 0 < centralMixedMinorMoment t S T p q := by
  unfold centralMixedMinorMoment
  exact mul_pos (centralDeterminantPowerMoment_pos _ _ _)
    (mul_pos (centralDeterminantPowerMoment_pos _ _ _) (centralDeterminantPowerMoment_pos _ _ _))

/-- The joint moment depends on both minor sizes AND their intersection, not independence. -/
theorem complexWishart_principalMinor_joint_norm_moment (t n : ℕ) (ht : n ≤ t)
    (S T : Finset (Fin n)) (p q : ℕ) :
    (∫⁻ W, ENNReal.ofReal (‖(W.submatrix (Subtype.val : S → Fin n) Subtype.val).det‖^p) *
        ENNReal.ofReal (‖(W.submatrix (Subtype.val : T → Fin n) Subtype.val).det‖^q)
      ∂complexWishart (m := t) (n := n)) =
        ENNReal.ofReal (centralMixedMinorMoment t S T p q) := by
  classical
  let R := finiteMinorOverlapModel S T
  let a := (S \ T).card
  let b := (T \ S).card
  let c := (S ∩ T).card
  have hS : a+c = S.card := finiteMinorOverlap_left_card S T
  have hT : b+c = T.card := finiteMinorOverlap_right_card S T
  have hs : S.card ≤ n := by simpa using Finset.card_le_card (Finset.subset_univ S)
  have ht' : T.card ≤ n := by simpa using Finset.card_le_card (Finset.subset_univ T)
  have hc : c ≤ t := by omega
  have hA : a ≤ t-c := by omega
  have hB : b ≤ t-c := by omega
  have h := complexWishart_embedded_overlap_moment t n (a+b) c a b p q
    R.embedding R.injective (Fin.castAdd b) (Fin.natAdd a)
    (show Function.Injective (Sum.elim (Fin.castAdd b) (Fin.natAdd a)) from finSumFinEquiv.injective)
    hc hA hB
  rw [R.left_eq,R.right_eq] at h
  have heS (W : Matrix (Fin n) (Fin n) ℂ) :
      (W.submatrix (Subtype.val ∘ R.left) (Subtype.val ∘ R.left)).det =
        (W.submatrix (Subtype.val : S → Fin n) Subtype.val).det := by
    change ((W.submatrix (Subtype.val : S → Fin n) Subtype.val).submatrix R.left R.left).det = _
    exact Matrix.det_submatrix_equiv_self R.left _
  have heT (W : Matrix (Fin n) (Fin n) ℂ) :
      (W.submatrix (Subtype.val ∘ R.right) (Subtype.val ∘ R.right)).det =
        (W.submatrix (Subtype.val : T → Fin n) Subtype.val).det := by
    change ((W.submatrix (Subtype.val : T → Fin n) Subtype.val).submatrix R.right R.right).det = _
    exact Matrix.det_submatrix_equiv_self R.right _
  simp_rw [heS,heT] at h
  rw [← ENNReal.ofReal_mul (centralDeterminantPowerMoment_pos _ _ _).le,
    ← ENNReal.ofReal_mul (centralDeterminantPowerMoment_pos _ _ _).le] at h
  exact h

theorem complexWishart_principalMinor_joint_re_moment (t n : ℕ) (ht : n ≤ t)
    (S T : Finset (Fin n)) (p q : ℕ) :
    (∫⁻ W, ENNReal.ofReal ((W.submatrix (Subtype.val : S → Fin n) Subtype.val).det.re^p) *
        ENNReal.ofReal ((W.submatrix (Subtype.val : T → Fin n) Subtype.val).det.re^q)
      ∂complexWishart (m := t) (n := n)) =
        ENNReal.ofReal (centralMixedMinorMoment t S T p q) := by
  rw [← complexWishart_principalMinor_joint_norm_moment t n ht S T p q]
  apply lintegral_congr_ae
  have hP : ∀ᵐ W ∂complexWishart (m := t) (n := n), W.PosSemidef :=
    (mem_ae_iff_prob_eq_one Matrix.posSemidef_is_closed.measurableSet).mpr
      complexWishart_measure_posSemidef
  filter_upwards [hP] with W hW
  rw [complex_norm_eq_re_of_nonneg _ (hW.submatrix _).det_nonneg,
    complex_norm_eq_re_of_nonneg _ (hW.submatrix _).det_nonneg]

end
end JinWishart
#print axioms JinWishart.centralMixedMinorMoment_pos
#print axioms JinWishart.complexWishart_principalMinor_joint_norm_moment
#print axioms JinWishart.complexWishart_principalMinor_joint_re_moment
