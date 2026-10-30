import JinWishartFormalization.DominatedLocalLaplaceUniqueness
import JinWishartFormalization.CandidateActualTraceTransform

/-! Codex. Seed 2026102508 finite Laplace uniqueness controls precede source.
One-dimensional nonnegative support specialization of the existing generic
tilt theorem. [需人工审查] AE support and local analytic uniqueness. -/
open MeasureTheory Matrix ProbabilityTheory Finset
open scoped ComplexOrder
namespace JinWishart
noncomputable section

theorem nonnegative_measure_eq_of_laplace_eq
 {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
 (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (hν : ∀ᵐ x ∂ν, 0 ≤ x)
 (hLaplace : ∀ s : ℝ, 0 ≤ s →
   (∫ x, Real.exp (-s*x) ∂μ) = ∫ x, Real.exp (-s*x) ∂ν) : μ = ν := by
 apply eq_of_norm_dominated_localLaplace (f := fun x : ℝ => x) (by fun_prop)
 · filter_upwards [hμ] with x hx
   simpa [Real.norm_eq_abs,abs_of_nonneg hx]
 · filter_upwards [hν] with x hx
   simpa [Real.norm_eq_abs,abs_of_nonneg hx]
 · intro A hA
   have hA1 : |A 1| < 1 := by
     have h := A.le_opNorm (1 : ℝ)
     simp only [Real.norm_eq_abs,abs_one,mul_one] at h
     exact lt_of_le_of_lt h hA
   have hs : 0 ≤ 1 - A 1 := by
     have := (abs_lt.mp hA1).2
     linarith
   have hlinear (x : ℝ) : A x = (A 1)*x := by
     have h := A.map_smul x (1 : ℝ)
     simpa [smul_eq_mul,mul_comm] using h
   have h := hLaplace (1-A 1) hs
   convert h using 1 <;> apply integral_congr_ae <;>
     filter_upwards [] with x <;> rw [hlinear] <;> congr 1 <;> ring

theorem map_eq_of_nonnegative_laplace_eq
 {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
 {μ : Measure Ω} {ν : Measure Ω'} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
 {X : Ω → ℝ} {Y : Ω' → ℝ} (hX : AEMeasurable X μ) (hY : AEMeasurable Y ν)
 (hXpos : ∀ᵐ x ∂μ, 0 ≤ X x) (hYpos : ∀ᵐ y ∂ν, 0 ≤ Y y)
 (hLaplace : ∀ s : ℝ, 0 ≤ s →
   (∫ x, Real.exp (-s*X x) ∂μ) = ∫ y, Real.exp (-s*Y y) ∂ν) :
 μ.map X = ν.map Y := by
 haveI : IsFiniteMeasure (μ.map X) := Measure.isFiniteMeasure_map _ _
 haveI : IsFiniteMeasure (ν.map Y) := Measure.isFiniteMeasure_map _ _
 apply nonnegative_measure_eq_of_laplace_eq
 · exact (ae_map_iff hX measurableSet_Ici).2 hXpos
 · exact (ae_map_iff hY measurableSet_Ici).2 hYpos
 · intro s hs
   rw [integral_map hX (by fun_prop),integral_map hY (by fun_prop)]
   exact hLaplace s hs

theorem mixedCandidateEnsemble_coordinates_positive_ae (p L q : ℕ) (lambda : Fin L → ℝ) :
 ∀ᵐ z ∂mixedCandidateEnsemble p L q lambda, ∀ i, 0 < z i := by
 let μ : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
 have hbase : ∀ᵐ z ∂Measure.pi (fun _ : Fin (p+L) => μ), ∀ i, 0 < z i := by
   apply Filter.eventually_all.2
   intro i
   exact Measure.tendsto_eval_ae_ae.eventually (ae_restrict_mem measurableSet_Ioi)
 have hac : mixedCandidateEnsemble p L q lambda ≪ Measure.pi (fun _ : Fin (p+L) => μ) := by
   unfold mixedCandidateEnsemble normalizedDeterminantEnsemble determinantEnsembleMeasure
   exact Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)
 exact hac.ae_le hbase

theorem candidate_actual_trace_law_equal (p L q : ℕ) (lambda : Fin L → ℝ)
 (hl : StrictMono lambda) (hlp : ∀ j, 0 < lambda j)
 (M : Matrix (Fin (p+L+q)) (Fin (p+L)) ℂ)
 (hmean : (∑ a : Fin (p+L+q) × Fin (p+L), ‖M a.1 a.2‖^2) = ∑ j : Fin L, lambda j) :
 (mixedCandidateEnsemble p L q lambda).map (fun z => ∑ i, z i) =
 (stdGaussian (ComplexSample (m := p+L+q) (n := p+L))).map
   (fun z => ∑ j : Fin (p+L), (complexGram (complexSampleMatrix z+M) j j).re) := by
 letI := mixedCandidateEnsemble_probability p L q lambda hl hlp
 have hX : Measurable (fun z : Fin (p+L) → ℝ => ∑ i, z i) := by fun_prop
 have hY : Measurable (fun z : ComplexSample (m := p+L+q) (n := p+L) =>
     ∑ j : Fin (p+L), (complexGram (complexSampleMatrix z+M) j j).re) := by
   apply Finset.measurable_sum
   intro j _
   exact Complex.continuous_re.measurable.comp ((measurable_pi_apply j).comp
     ((measurable_pi_apply j).comp (measurable_shiftedComplexSampleGram M)))
 apply map_eq_of_nonnegative_laplace_eq hX.aemeasurable hY.aemeasurable
 · filter_upwards [mixedCandidateEnsemble_coordinates_positive_ae p L q lambda] with z hz
   exact Finset.sum_nonneg (fun i _ => (hz i).le)
 · filter_upwards [] with z
   have h := (RCLike.nonneg_iff.mp (complexGram_posSemidef (complexSampleMatrix z+M)).trace_nonneg).1
   simpa [Matrix.trace,Complex.re_sum] using h
 · exact candidate_actual_trace_laplace_equal p L q lambda hl hlp M hmean

end
end JinWishart
#print axioms JinWishart.nonnegative_measure_eq_of_laplace_eq
#print axioms JinWishart.map_eq_of_nonnegative_laplace_eq
#print axioms JinWishart.mixedCandidateEnsemble_coordinates_positive_ae
#print axioms JinWishart.candidate_actual_trace_law_equal
