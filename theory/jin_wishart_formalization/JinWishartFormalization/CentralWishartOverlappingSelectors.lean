import JinWishartFormalization.CentralWishartSharedPrefix

/-!
# Mixed moments under arbitrary embeddings of the shared-column configuration

Codex proof bodies. The common columns can occur anywhere in the original sample.
[需人工审查] Actual column selection and common/exclusive index interpretation.
-/
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace JinWishart
noncomputable section

theorem complexWishart_pair_minor_selection_integral (t n u a b p q : ℕ)
    (h : Fin u → Fin n) (hh : Function.Injective h)
    (e : Fin a → Fin u) (f : Fin b → Fin u) :
    (∫⁻ A, ENNReal.ofReal (‖(A.submatrix (h ∘ e) (h ∘ e)).det‖^p) *
        ENNReal.ofReal (‖(A.submatrix (h ∘ f) (h ∘ f)).det‖^q)
      ∂complexWishart (m := t) (n := n)) =
      ∫⁻ B, ENNReal.ofReal (‖(B.submatrix e e).det‖^p) *
        ENNReal.ofReal (‖(B.submatrix f f).det‖^q)
        ∂complexWishart (m := t) (n := u) := by
  have hM := congrArg (fun μ => ∫⁻ A, ENNReal.ofReal (‖(A.submatrix e e).det‖^p) *
    ENNReal.ofReal (‖(A.submatrix f f).det‖^q) ∂μ)
      (complexWishart_principalSubmatrix_law (m := t) h hh)
  rw [lintegral_map (by fun_prop) (by fun_prop)] at hM
  simpa only [Function.comp_apply, Matrix.submatrix_submatrix] using hM

/-- Actual closed mixed moment for an arbitrarily embedded common-column pattern.
No factorization of dependent minors is postulated. The common moment uses p+q. -/
theorem complexWishart_embedded_overlap_moment (t n u c a b p q : ℕ)
    (h : Fin (u+c) → Fin n) (hh : Function.Injective h)
    (e : Fin a → Fin u) (f : Fin b → Fin u)
    (hef : Function.Injective (Sum.elim e f))
    (hc : c ≤ t) (ha : a ≤ t-c) (hb : b ≤ t-c) :
    (∫⁻ A, ENNReal.ofReal (‖(A.submatrix
          (h ∘ centralSharedPrefixSelection c e)
          (h ∘ centralSharedPrefixSelection c e)).det‖^p) *
        ENNReal.ofReal (‖(A.submatrix
          (h ∘ centralSharedPrefixSelection c f)
          (h ∘ centralSharedPrefixSelection c f)).det‖^q)
      ∂complexWishart (m := t) (n := n)) =
      ENNReal.ofReal (centralDeterminantPowerMoment (t-c) c (p+q)) *
        (ENNReal.ofReal (centralDeterminantPowerMoment (t-c-a) a p) *
          ENNReal.ofReal (centralDeterminantPowerMoment (t-c-b) b q)) := by
  rw [complexWishart_pair_minor_selection_integral t n (u+c) (a+c) (b+c) p q h hh]
  have hP := complexWishart_common_prefix_disjoint_moment (t-c) u c a b p q e f hef ha hb
  simpa only [Nat.sub_add_cancel hc] using hP

end
end JinWishart
#print axioms JinWishart.complexWishart_pair_minor_selection_integral
#print axioms JinWishart.complexWishart_embedded_overlap_moment
