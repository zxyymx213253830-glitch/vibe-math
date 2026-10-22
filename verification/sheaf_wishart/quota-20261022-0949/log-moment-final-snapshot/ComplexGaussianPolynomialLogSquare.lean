import JinWishartFormalization.ComplexGaussianRootLogMoments
import JinWishartFormalization.ComplexGaussianPolynomialLog
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.BigOperators.Fin

/-! One-variable polynomial negative-log square, with degree/coefficient bound.
Root multiplicities are retained; no parameterized measurable root choice.
Codex. [需人工审查] Root factorization, Gaussian normalization and integration. -/
open MeasureTheory ProbabilityTheory Finset
namespace JinWishart
noncomputable section

theorem complexNegativeLog_finset_prod_le_sum {ι : Type*} (s : Finset ι) (f : ι→ℂ) :
    complexNegativeLog (∏ i∈s,f i)≤∑ i∈s,complexNegativeLog (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [complexNegativeLog]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi,Finset.sum_insert hi]
    exact (complexNegativeLog_mul_le _ _).trans (add_le_add le_rfl ih)

theorem stdGaussian_complex_finite_rootProduct_negativeLog_sq {ι : Type*} [Fintype ι]
    (roots : ι→ℂ) :
    Integrable (fun z : ℂ => (complexNegativeLog (∏ i,(z-roots i)))^2) (stdGaussian ℂ) ∧
      (∫ z : ℂ,(complexNegativeLog (∏ i,(z-roots i)))^2 ∂stdGaussian ℂ)≤(Fintype.card ι : ℝ)^2/4 := by
  classical
  have hi (i : ι) := (stdGaussian_complex_negativeLog_sq_uniform_root (roots i)).1
  have hdom := (integrable_finsetSum Finset.univ (fun i _ => hi i)).const_mul (Fintype.card ι : ℝ)
  have hb (z : ℂ) : (complexNegativeLog (∏ i,(z-roots i)))^2≤
      (Fintype.card ι : ℝ)*(∑ i,(complexNegativeLog (z-roots i))^2) := by
    have h := pow_le_pow_left₀ (le_max_left (0:ℝ) _) (complexNegativeLog_finset_prod_le_sum Finset.univ (fun i=>z-roots i)) 2
    exact h.trans (by simpa using (_root_.sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun i=>complexNegativeLog (z-roots i))))
  have hm : Measurable (fun z : ℂ => (complexNegativeLog (∏ i,(z-roots i)))^2) := by
    unfold complexNegativeLog
    fun_prop
  have hint := hdom.mono' hm.aestronglyMeasurable (ae_of_all _ (fun z=>by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact hb z))
  refine ⟨hint,?_⟩
  calc
    _ ≤ ∫ z : ℂ,(Fintype.card ι : ℝ)*(∑ i,(complexNegativeLog (z-roots i))^2) ∂stdGaussian ℂ :=
      integral_mono_ae hint hdom (ae_of_all _ hb)
    _ = (Fintype.card ι : ℝ)*(∑ i,∫ z : ℂ,(complexNegativeLog (z-roots i))^2 ∂stdGaussian ℂ) := by
      rw [integral_const_mul,integral_finsetSum _ (fun i _=>hi i)]
    _ ≤ (Fintype.card ι : ℝ)*(∑ _i : ι,(1/4:ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum (fun i _=>(stdGaussian_complex_negativeLog_sq_uniform_root (roots i)).2)
    _ = _ := by simp; ring

theorem stdGaussian_complex_polynomial_negativeLog_sq (P : Polynomial ℂ) :
    Integrable (fun z : ℂ => (complexNegativeLog (P.eval z))^2) (stdGaussian ℂ) ∧
      (∫ z : ℂ,(complexNegativeLog (P.eval z))^2 ∂stdGaussian ℂ)≤
        2*(complexNegativeLog P.leadingCoeff)^2+(P.natDegree : ℝ)^2/2 := by
  classical
  let l := P.roots.toList
  let roots : Fin l.length→ℂ := l.get
  have hprod (z : ℂ) : (l.map (fun a=>z-a)).prod=∏ i,(z-roots i) := by
    rw [← List.prod_ofFn]
    congr 1
    exact (List.ofFn_getElem_eq_map l (fun a=>z-a)).symm
  have heval (z : ℂ) : P.eval z=P.leadingCoeff*(∏ i,(z-roots i)) := by
    rw [← hprod]
    rw [(IsAlgClosed.splits P).eval_eq_prod_roots]
    simp only [l,Multiset.prod_map_toList]
  have hroot := stdGaussian_complex_finite_rootProduct_negativeLog_sq roots
  have hD : (Fintype.card (Fin l.length) : ℝ)=(P.natDegree : ℝ) := by
    simp only [Fintype.card_fin,l,Multiset.length_toList,(IsAlgClosed.splits P).natDegree_eq_card_roots]
  rw [hD] at hroot
  have hdom := (integrable_const (2*(complexNegativeLog P.leadingCoeff)^2) :
    Integrable (fun _z : ℂ=>2*(complexNegativeLog P.leadingCoeff)^2) (stdGaussian ℂ)).add (hroot.1.const_mul 2)
  have hb (z : ℂ) : (complexNegativeLog (P.eval z))^2≤
      2*(complexNegativeLog P.leadingCoeff)^2+2*(complexNegativeLog (∏ i,(z-roots i)))^2 := by
    have hy := complexNegativeLog_finset_prod_le_sum Finset.univ (fun i=>z-roots i)
    have h := complexNegativeLog_mul_le P.leadingCoeff (∏ i,(z-roots i))
    rw [← heval] at h
    have hs := pow_le_pow_left₀ (le_max_left (0:ℝ) _) h 2
    change (complexNegativeLog (P.eval z))^2≤_ at hs
    nlinarith [sq_nonneg (complexNegativeLog P.leadingCoeff-complexNegativeLog (∏ i,(z-roots i)))]
  have hm : Measurable (fun z : ℂ => (complexNegativeLog (P.eval z))^2) :=
    (measurable_const.max P.continuous.norm.measurable.log.neg).pow_const 2
  have hint := hdom.mono' hm.aestronglyMeasurable (ae_of_all _ (fun z=>by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact hb z))
  refine ⟨hint,?_⟩
  calc
    _ ≤ ∫ z : ℂ,2*(complexNegativeLog P.leadingCoeff)^2+2*(complexNegativeLog (∏ i,(z-roots i)))^2 ∂stdGaussian ℂ :=
      integral_mono_ae hint hdom (ae_of_all _ hb)
    _ = 2*(complexNegativeLog P.leadingCoeff)^2+2*(∫ z : ℂ,(complexNegativeLog (∏ i,(z-roots i)))^2 ∂stdGaussian ℂ) := by
      rw [integral_add (integrable_const _) (hroot.1.const_mul 2)]
      simp [integral_const_mul]
    _ ≤ _ := by nlinarith [hroot.2]

end
end JinWishart
#print axioms JinWishart.complexNegativeLog_finset_prod_le_sum
#print axioms JinWishart.stdGaussian_complex_finite_rootProduct_negativeLog_sq
#print axioms JinWishart.stdGaussian_complex_polynomial_negativeLog_sq
