import JinWishartFormalization.CandidateSpectralTraceLaw
import JinWishartFormalization.ActualGaussianTraceVariance

/-! Codex. Seed 2026103101 actual trace moment controls precede source.
Candidate scalar-trace moments transported from actual Gram trace law only.
[需人工审查] Fubini, Bochner transport and paper/model mapping. -/
open Matrix MeasureTheory ProbabilityTheory Finset
namespace JinWishart
noncomputable section

theorem candidate_actual_trace_integral_transfer (p L q : ℕ) (lambda : Fin L → ℝ)
 (hl : StrictMono lambda) (hlp : ∀ j, 0 < lambda j)
 (M : Matrix (Fin (p+L+q)) (Fin (p+L)) ℂ)
 (hmean : (∑ a : Fin (p+L+q) × Fin (p+L), ‖M a.1 a.2‖^2) = ∑ j : Fin L, lambda j)
 (F : ℝ → ℝ) (hF : Continuous F) :
 (∫ z : Fin (p+L) → ℝ, F (∑ i, z i) ∂(mixedCandidateEnsemble p L q lambda)) =
 (∫ z : ComplexSample (m := p+L+q) (n := p+L),
    F ((complexGram (complexSampleMatrix z+M)).trace.re)
    ∂stdGaussian (ComplexSample (m := p+L+q) (n := p+L))) := by
 have hX : Measurable (fun z : Fin (p+L) → ℝ => ∑ i, z i) := by fun_prop
 have hY : Measurable (fun z : ComplexSample (m := p+L+q) (n := p+L) =>
     ∑ j : Fin (p+L), (complexGram (complexSampleMatrix z+M) j j).re) := by
   apply Finset.measurable_sum
   intro j _
   exact Complex.continuous_re.measurable.comp ((measurable_pi_apply j).comp
     ((measurable_pi_apply j).comp (measurable_shiftedComplexSampleGram M)))
 have h := congrArg (fun μ : Measure ℝ => ∫ x, F x ∂μ)
   (candidate_actual_trace_law_equal p L q lambda hl hlp M hmean)
 rw [integral_map hX.aemeasurable hF.measurable.aestronglyMeasurable,
   integral_map hY.aemeasurable hF.measurable.aestronglyMeasurable] at h
 simpa [Matrix.trace,Complex.re_sum] using h

theorem candidate_actual_trace_integrable_transfer (p L q : ℕ) (lambda : Fin L → ℝ)
 (hl : StrictMono lambda) (hlp : ∀ j, 0 < lambda j)
 (M : Matrix (Fin (p+L+q)) (Fin (p+L)) ℂ)
 (hmean : (∑ a : Fin (p+L+q) × Fin (p+L), ‖M a.1 a.2‖^2) = ∑ j : Fin L, lambda j)
 (F : ℝ → ℝ) (hF : Continuous F)
 (hI : Integrable (fun z : ComplexSample (m := p+L+q) (n := p+L) =>
   F ((complexGram (complexSampleMatrix z+M)).trace.re)) (stdGaussian _)) :
 Integrable (fun z : Fin (p+L) → ℝ => F (∑ i, z i)) (mixedCandidateEnsemble p L q lambda) := by
 let X : (Fin (p+L) → ℝ) → ℝ := fun z => ∑ i, z i
 let Y : ComplexSample (m := p+L+q) (n := p+L) → ℝ :=
   fun z => ∑ j : Fin (p+L), (complexGram (complexSampleMatrix z+M) j j).re
 have hX : Measurable X := by dsimp [X]; fun_prop
 have hY : Measurable Y := by
   dsimp [Y]
   apply Finset.measurable_sum
   intro j _
   exact Complex.continuous_re.measurable.comp ((measurable_pi_apply j).comp
     ((measurable_pi_apply j).comp (measurable_shiftedComplexSampleGram M)))
 have hI' : Integrable (F ∘ Y) (stdGaussian _) := by
   simpa [Y,Function.comp_def,Matrix.trace,Complex.re_sum] using hI
 have hp := (integrable_map_measure hF.measurable.aestronglyMeasurable hY.aemeasurable).2 hI'
 have hlaw := candidate_actual_trace_law_equal p L q lambda hl hlp M hmean
 change (mixedCandidateEnsemble p L q lambda).map X = (stdGaussian _).map Y at hlaw
 rw [← hlaw] at hp
 exact (integrable_map_measure hF.measurable.aestronglyMeasurable hX.aemeasurable).1 hp

theorem candidate_trace_integrable (p L q : ℕ) (lambda : Fin L → ℝ)
 (hl : StrictMono lambda) (hlp : ∀ j, 0 < lambda j)
 (M : Matrix (Fin (p+L+q)) (Fin (p+L)) ℂ)
 (hmean : (∑ a : Fin (p+L+q) × Fin (p+L), ‖M a.1 a.2‖^2) = ∑ j : Fin L, lambda j) :
 Integrable (fun z : Fin (p+L) → ℝ => ∑ i, z i) (mixedCandidateEnsemble p L q lambda) := by
 exact candidate_actual_trace_integrable_transfer p L q lambda hl hlp M hmean id continuous_id
   (integrable_actualNoncentralGram_trace M)

theorem candidate_trace_centered_sq_integrable (p L q : ℕ) (lambda : Fin L → ℝ)
 (hl : StrictMono lambda) (hlp : ∀ j, 0 < lambda j)
 (M : Matrix (Fin (p+L+q)) (Fin (p+L)) ℂ)
 (hmean : (∑ a : Fin (p+L+q) × Fin (p+L), ‖M a.1 a.2‖^2) = ∑ j : Fin L, lambda j)
 (T : ℝ) :
 Integrable (fun z : Fin (p+L) → ℝ => ((∑ i, z i)-T)^2) (mixedCandidateEnsemble p L q lambda) := by
 apply candidate_actual_trace_integrable_transfer p L q lambda hl hlp M hmean (fun x => (x-T)^2) (by fun_prop)
 have hi := (integrable_actualNoncentralGram_trace_sq M).sub
   ((integrable_actualNoncentralGram_trace M).const_mul (2*T))
 have hi := hi.add (integrable_const (T^2))
 convert hi using 1
 funext z
 simp only [Pi.add_apply,Pi.sub_apply]
 ring

theorem candidate_trace_mean (p L q : ℕ) (lambda : Fin L → ℝ)
 (hl : StrictMono lambda) (hlp : ∀ j, 0 < lambda j)
 (M : Matrix (Fin (p+L+q)) (Fin (p+L)) ℂ)
 (hmean : (∑ a : Fin (p+L+q) × Fin (p+L), ‖M a.1 a.2‖^2) = ∑ j : Fin L, lambda j) :
 (∫ z : Fin (p+L) → ℝ, ∑ i, z i ∂(mixedCandidateEnsemble p L q lambda)) =
 (((p+L)*(p+L+q) : ℕ) : ℝ) + ∑ j : Fin L, lambda j := by
 have h := candidate_actual_trace_integral_transfer p L q lambda hl hlp M hmean id continuous_id
 simp only [id_eq] at h
 change _ = actualExpectedGramPower M at h
 have henergy := hmean
 rw [Fintype.sum_prod_type] at henergy
 rw [h,actualExpectedGramPower_eq_closed,henergy]
 congr 1
 exact_mod_cast (Nat.mul_comm (p+L+q) (p+L))

theorem candidate_trace_centered_second_moment (p L q : ℕ) (lambda : Fin L → ℝ)
 (hl : StrictMono lambda) (hlp : ∀ j, 0 < lambda j)
 (M : Matrix (Fin (p+L+q)) (Fin (p+L)) ℂ)
 (hmean : (∑ a : Fin (p+L+q) × Fin (p+L), ‖M a.1 a.2‖^2) = ∑ j : Fin L, lambda j) :
 (∫ z : Fin (p+L) → ℝ,
   ((∑ i, z i) - (((p+L)*(p+L+q) : ℕ) : ℝ) - ∑ j : Fin L, lambda j)^2
   ∂(mixedCandidateEnsemble p L q lambda)) =
 (((p+L)*(p+L+q) : ℕ) : ℝ) + 2*(∑ j : Fin L, lambda j) := by
 let T : ℝ := (((p+L)*(p+L+q) : ℕ) : ℝ) + ∑ j : Fin L, lambda j
 have h := candidate_actual_trace_integral_transfer p L q lambda hl hlp M hmean
   (fun x => (x-T)^2) (by fun_prop)
 have henergy := hmean
 rw [Fintype.sum_prod_type] at henergy
 have hT : T = (((p+L+q)*(p+L) : ℕ) : ℝ) + ∑ i, ∑ j, ‖M i j‖^2 := by
   dsimp [T]
   rw [henergy]
   congr 1
   exact_mod_cast (Nat.mul_comm (p+L) (p+L+q))
 rw [hT,integral_actualNoncentralGram_trace_centered_sq] at h
 simp only [henergy] at h
 have hmul : (((p+L+q)*(p+L) : ℕ) : ℝ) = (((p+L)*(p+L+q) : ℕ) : ℝ) := by
   exact_mod_cast (Nat.mul_comm (p+L+q) (p+L))
 rw [hmul] at h
 simpa [T,sub_add_eq_sub_sub] using h

end
end JinWishart
#print axioms JinWishart.candidate_actual_trace_integral_transfer
#print axioms JinWishart.candidate_actual_trace_integrable_transfer
#print axioms JinWishart.candidate_trace_integrable
#print axioms JinWishart.candidate_trace_centered_sq_integrable
#print axioms JinWishart.candidate_trace_mean
#print axioms JinWishart.candidate_trace_centered_second_moment
