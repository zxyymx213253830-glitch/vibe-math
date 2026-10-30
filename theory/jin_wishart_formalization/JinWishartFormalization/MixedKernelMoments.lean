import JinWishartFormalization.InfiniteNoncentralKernel
import JinWishartFormalization.PoissonFactorialMoments
import JinWishartFormalization.NegativeLogNaturalMomentBounds

/-! Codex. Seed 2026103003 independent quadrature checks precede source.
Scalar moments of the entire series kernel only. [需人工审查] Fubini, absolute
integrability and correspondence to the matrix model. -/
open MeasureTheory Set
open Finset
namespace JinWishart
noncomputable section

def scalarSeriesKernel (q : ℕ) (lambda t : ℝ) : ℝ :=
 ∑' m : ℕ, t^m*(noncentralKernelSeriesWeight q m*lambda^m)

private def mixedMomentTerm (q k : ℕ) (lambda : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
 (lambda^m/((m.factorial : ℝ)*((q+m).factorial : ℝ)))*
   (t^(m+q+k)*Real.exp (-t))

private theorem mixedMomentTerm_integrable (q k : ℕ) (lambda : ℝ) (m : ℕ) :
 IntegrableOn (mixedMomentTerm q k lambda m) (Ioi 0) := by
 exact (integral_natPower_exp_neg_Ioi (m+q+k)).1.const_mul _

private theorem mixedMomentTerm_integral (q k : ℕ) (lambda : ℝ) (m : ℕ) :
 (∫ t in Ioi (0 : ℝ), mixedMomentTerm q k lambda m t) =
   (lambda^m/(m.factorial : ℝ)) *
     (((m+q+k).factorial : ℝ)/((m+q).factorial : ℝ)) := by
 unfold mixedMomentTerm
 rw [integral_const_mul,(integral_natPower_exp_neg_Ioi (m+q+k)).2]
 have hm : (m.factorial : ℝ) ≠ 0 := by positivity
 have hmq : ((m+q).factorial : ℝ) ≠ 0 := by positivity
 rw [Nat.add_comm q m]
 field_simp

theorem scalarSeriesKernel_weightedMoment (q k : ℕ) (lambda : ℝ) (hl : 0 ≤ lambda) :
 IntegrableOn (fun t : ℝ => t^(q+k)*Real.exp (-t)*scalarSeriesKernel q lambda t) (Ioi 0) ∧
 (∫ t in Ioi (0 : ℝ), t^(q+k)*Real.exp (-t)*scalarSeriesKernel q lambda t) =
   Real.exp lambda * poissonFactorialMomentPolynomial q k lambda := by
 let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
 have hF : ∀ m : ℕ, Integrable (mixedMomentTerm q k lambda m) μ :=
   fun m => mixedMomentTerm_integrable q k lambda m
 have hnorm (m : ℕ) : (∫ t, ‖mixedMomentTerm q k lambda m t‖ ∂μ) =
   (lambda^m/(m.factorial : ℝ))*(((m+q+k).factorial : ℝ)/((m+q).factorial : ℝ)) := by
   calc
     _ = ∫ t, mixedMomentTerm q k lambda m t ∂μ := by
       apply integral_congr_ae
       filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
       rw [Real.norm_eq_abs,abs_of_nonneg]
       unfold mixedMomentTerm
       have ht0 : 0 < t := ht
       positivity
     _ = _ := mixedMomentTerm_integral q k lambda m
 have hsum : Summable (fun m : ℕ => ∫ t, ‖mixedMomentTerm q k lambda m t‖ ∂μ) := by
   apply (poisson_factorialMoment_hasSum q k lambda).summable.congr
   intro m
   exact (hnorm m).symm
 have he (t : ℝ) : (∑' m : ℕ, mixedMomentTerm q k lambda m t) =
     t^(q+k)*Real.exp (-t)*scalarSeriesKernel q lambda t := by
   unfold scalarSeriesKernel
   rw [← tsum_mul_left]
   apply tsum_congr
   intro m
   unfold mixedMomentTerm noncentralKernelSeriesWeight
   rw [pow_add]
   ring
 have hI : (∫ t, (∑' m, mixedMomentTerm q k lambda m t) ∂μ) =
     Real.exp lambda * poissonFactorialMomentPolynomial q k lambda := by
   calc
     _ = ∑' m, (∫ t, mixedMomentTerm q k lambda m t ∂μ) :=
       (integral_tsum_of_summable_integral_norm hF hsum).symm
     _ = ∑' m : ℕ, (lambda^m/(m.factorial : ℝ))*
         (((m+q+k).factorial : ℝ)/((m+q).factorial : ℝ)) := by
       apply tsum_congr
       intro m
       exact mixedMomentTerm_integral q k lambda m
     _ = _ := (poisson_factorialMoment_hasSum q k lambda).tsum_eq
 have hp : 0 < poissonFactorialMomentPolynomial q k lambda := by
   unfold poissonFactorialMomentPolynomial
   apply mul_pos (by positivity)
   have hc : 0 < ((q+k).choose k : ℝ) := by
     exact_mod_cast Nat.choose_pos (show k ≤ q+k by omega)
   have hs := single_le_sum
     (f := fun j : ℕ => ((q+k).choose (k-j) : ℝ)*lambda^j/(j.factorial : ℝ))
     (s := range (k+1)) (fun j _ => by positivity)
     (show 0 ∈ range (k+1) by simp)
   simp only [Nat.sub_zero,pow_zero,Nat.factorial_zero,Nat.cast_one,div_one,mul_one] at hs
   exact lt_of_lt_of_le hc hs
 have htarget : (∫ t in Ioi (0 : ℝ), t^(q+k)*Real.exp (-t)*scalarSeriesKernel q lambda t) =
     Real.exp lambda * poissonFactorialMomentPolynomial q k lambda := by
   rw [← funext he]
   exact hI
 constructor
 · apply Integrable.of_integral_ne_zero
   rw [htarget]
   exact ne_of_gt (mul_pos (Real.exp_pos _) hp)
 · exact htarget

end
end JinWishart
#print axioms JinWishart.scalarSeriesKernel_weightedMoment
