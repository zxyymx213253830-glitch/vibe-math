import JinWishartFormalization.ComplexGaussianRootNegativeLog
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-! One-variable complex polynomial logarithms under stdGaussian(C).
Real.log is totalized at zero; in particular the zero polynomial is harmless
for these literal statements. No multivariate or randomly selected roots.
Codex. [需人工审查] Root multiplicity, Gaussian normalization, integration.
-/
open MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

theorem stdGaussian_complex_rootProduct_negativeLog (l : List ℂ) :
    Integrable (fun z : ℂ => complexNegativeLog ((l.map (fun r => z-r)).prod))
      (stdGaussian ℂ) ∧
    (∫ z : ℂ, complexNegativeLog ((l.map (fun r => z-r)).prod) ∂stdGaussian ℂ)
      ≤ (l.length : ℝ)/4 := by
  have hcont (s : List ℂ) : Continuous (fun z : ℂ => (s.map (fun r => z-r)).prod) := by
    induction s with
    | nil => simpa using (continuous_const : Continuous (fun _z : ℂ => (1 : ℂ)))
    | cons r s ih =>
      simp only [List.map_cons,List.prod_cons]
      fun_prop
  induction l with
  | nil =>
    constructor
    · simpa [complexNegativeLog] using
        (integrable_const (0 : ℝ) : Integrable (fun _z : ℂ => 0) (stdGaussian ℂ))
    · simp [complexNegativeLog]
  | cons r l ih =>
    have hr := stdGaussian_complex_negativeLog_uniform_root r
    have hm : Measurable (fun z : ℂ => complexNegativeLog (((r::l).map (fun a => z-a)).prod)) :=
      measurable_const.max ((hcont (r::l)).norm.measurable.log.neg)
    have hb (z : ℂ) :
        complexNegativeLog ((((r::l).map (fun a => z-a))).prod) ≤
          complexNegativeLog (z-r)+complexNegativeLog ((l.map (fun a => z-a)).prod) := by
      simpa only [List.map_cons,List.prod_cons] using
        complexNegativeLog_mul_le (z-r) ((l.map (fun a => z-a)).prod)
    have hi := (hr.1.add ih.1).mono' hm.aestronglyMeasurable (ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (le_max_left _ _)]
      exact hb z))
    refine ⟨hi, ?_⟩
    calc
      _ ≤ ∫ z : ℂ, complexNegativeLog (z-r)+complexNegativeLog ((l.map (fun a => z-a)).prod)
          ∂stdGaussian ℂ := integral_mono_ae hi (hr.1.add ih.1) (ae_of_all _ hb)
      _ = (∫ z : ℂ, complexNegativeLog (z-r) ∂stdGaussian ℂ)+
          (∫ z : ℂ, complexNegativeLog ((l.map (fun a => z-a)).prod) ∂stdGaussian ℂ) :=
        integral_add hr.1 ih.1
      _ ≤ 1/4+(l.length : ℝ)/4 := add_le_add hr.2 ih.2
      _ = ((r::l).length : ℝ)/4 := by simp only [List.length_cons,Nat.cast_add,Nat.cast_one]; ring

theorem stdGaussian_complex_polynomial_negativeLog (P : Polynomial ℂ) :
    Integrable (fun z : ℂ => complexNegativeLog (P.eval z)) (stdGaussian ℂ) ∧
    (∫ z : ℂ, complexNegativeLog (P.eval z) ∂stdGaussian ℂ) ≤
      complexNegativeLog P.leadingCoeff + (P.natDegree : ℝ)/4 := by
  classical
  let l := P.roots.toList
  have heval (z : ℂ) : P.eval z = P.leadingCoeff*(l.map (fun r => z-r)).prod := by
    rw [(IsAlgClosed.splits P).eval_eq_prod_roots]
    simp only [l,Multiset.prod_map_toList]
  have hr := stdGaussian_complex_rootProduct_negativeLog l
  have hc : Integrable (fun _z : ℂ => complexNegativeLog P.leadingCoeff) (stdGaussian ℂ) :=
    integrable_const _
  have hm : Measurable (fun z : ℂ => complexNegativeLog (P.eval z)) :=
    measurable_const.max (P.continuous.norm.measurable.log.neg)
  have hb (z : ℂ) : complexNegativeLog (P.eval z) ≤
      complexNegativeLog P.leadingCoeff + complexNegativeLog ((l.map (fun r => z-r)).prod) := by
    rw [heval]
    exact complexNegativeLog_mul_le _ _
  have hi := (hc.add hr.1).mono' hm.aestronglyMeasurable (ae_of_all _ (fun z => by
    rw [Real.norm_eq_abs,abs_of_nonneg (le_max_left _ _)]
    exact hb z))
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ z : ℂ, complexNegativeLog P.leadingCoeff +
        complexNegativeLog ((l.map (fun r => z-r)).prod) ∂stdGaussian ℂ :=
      integral_mono_ae hi (hc.add hr.1) (ae_of_all _ hb)
    _ = complexNegativeLog P.leadingCoeff+
        (∫ z : ℂ, complexNegativeLog ((l.map (fun r => z-r)).prod) ∂stdGaussian ℂ) := by
      rw [integral_add hc hr.1]
      simp
    _ ≤ complexNegativeLog P.leadingCoeff+(l.length : ℝ)/4 := add_le_add le_rfl hr.2
    _ = complexNegativeLog P.leadingCoeff+(P.natDegree : ℝ)/4 := by
      simp only [l,Multiset.length_toList,(IsAlgClosed.splits P).natDegree_eq_card_roots]

theorem integrable_stdGaussian_complex_polynomial_eval (P : Polynomial ℂ) :
    Integrable (fun z : ℂ => P.eval z) (stdGaussian ℂ) := by
  classical
  have hk (k : ℕ) : Integrable (fun z : ℂ => z^k) (stdGaussian ℂ) := by
    have hm : MemLp (id : ℂ → ℂ) k (stdGaussian ℂ) := IsGaussian.memLp_id _ _ (by simp)
    apply hm.integrable_norm_pow'.mono' (by fun_prop)
    exact ae_of_all _ (fun z => by simp only [norm_pow,id_eq]; exact le_rfl)
  simp_rw [Polynomial.eval_eq_sum,Polynomial.sum_def]
  apply integrable_finsetSum
  intro k _
  exact (hk k).const_mul _

theorem stdGaussian_complex_polynomial_log_integrable (P : Polynomial ℂ) :
    Integrable (fun z : ℂ => Real.log ‖P.eval z‖) (stdGaussian ℂ) := by
  have hf := (integrable_stdGaussian_complex_polynomial_eval P).norm
  have hn := (stdGaussian_complex_polynomial_negativeLog P).1
  apply (hf.add hn).mono' P.continuous.norm.measurable.log.aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs]
  change |Real.log ‖P.eval z‖| ≤ ‖P.eval z‖ + max 0 (-Real.log ‖P.eval z‖)
  by_cases hz : P.eval z=0
  · simp [hz]
  have hpos : 0 < ‖P.eval z‖ := norm_pos_iff.mpr hz
  have hu := Real.log_le_sub_one_of_pos hpos
  have h1 := le_max_left (0 : ℝ) (-Real.log ‖P.eval z‖)
  have h2 := le_max_right (0 : ℝ) (-Real.log ‖P.eval z‖)
  have hnorm := norm_nonneg (P.eval z)
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end
end JinWishart
#print axioms JinWishart.stdGaussian_complex_rootProduct_negativeLog
#print axioms JinWishart.stdGaussian_complex_polynomial_negativeLog
#print axioms JinWishart.integrable_stdGaussian_complex_polynomial_eval
#print axioms JinWishart.stdGaussian_complex_polynomial_log_integrable
