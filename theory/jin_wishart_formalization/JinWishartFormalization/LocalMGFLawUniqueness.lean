import Mathlib.Probability.Moments.ComplexMGF

/-! Codex. Seed 2026102251 controls precede source.
[需人工审查] Common analytic strip, local identity theorem, AE pushforwards.
This is a generic law bridge, not an actual Gaussian radial law. -/
open MeasureTheory Filter Set Complex ProbabilityTheory
open scoped Topology
namespace JinWishart
noncomputable section

theorem map_eq_of_mgf_eventuallyEq_zero
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {ν : Measure Ω'} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {X : Ω → ℝ} {Y : Ω' → ℝ}
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y ν)
    (h0X : 0 ∈ interior (integrableExpSet X μ))
    (h0Y : 0 ∈ interior (integrableExpSet Y ν))
    (hmgf : mgf X μ =ᶠ[𝓝 0] mgf Y ν) :
    μ.map X = ν.map Y := by
  let U : Set ℂ := {z | z.re ∈ interior (integrableExpSet X μ) ∩
    interior (integrableExpSet Y ν)}
  have hAX : AnalyticOnNhd ℂ (complexMGF X μ) U :=
    analyticOnNhd_complexMGF.mono (fun _ hz => hz.1)
  have hAY : AnalyticOnNhd ℂ (complexMGF Y ν) U :=
    analyticOnNhd_complexMGF.mono (fun _ hz => hz.2)
  have hU : IsPreconnected U :=
    ((convex_integrableExpSet (X := X) (μ := μ)).interior.inter
      (convex_integrableExpSet (X := Y) (μ := ν)).interior).linear_preimage
        reLm |>.isPreconnected
  have hreal : ∃ᶠ (x : ℝ) in 𝓝[≠] (0 : ℝ),
      complexMGF X μ x = complexMGF Y ν x := by
    have he : ∀ᶠ x in 𝓝[≠] (0 : ℝ), mgf X μ x = mgf Y ν x :=
      hmgf.filter_mono nhdsWithin_le_nhds
    exact he.frequently.mono (fun x hx => by
      simpa only [complexMGF_ofReal] using congrArg (fun r : ℝ => (r : ℂ)) hx)
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), complexMGF X μ z = complexMGF Y ν z := by
    rw [frequently_iff_seq_forall] at hreal ⊢
    obtain ⟨xs, hx, he⟩ := hreal
    refine ⟨fun n => (xs n : ℂ), ?_, fun n => he n⟩
    rw [tendsto_nhdsWithin_iff] at hx ⊢
    constructor
    · change Tendsto (fun n => (xs n : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ))
      rw [tendsto_ofReal_iff]
      exact hx.1
    · simpa using hx.2
  have hEq : EqOn (complexMGF X μ) (complexMGF Y ν) U :=
    hAX.eqOn_of_preconnected_of_frequently_eq hAY hU
      (z₀ := 0) (by simpa [U] using And.intro h0X h0Y) hfreq
  haveI : IsFiniteMeasure (μ.map X) := Measure.isFiniteMeasure_map _ _
  haveI : IsFiniteMeasure (ν.map Y) := Measure.isFiniteMeasure_map _ _
  apply Measure.ext_of_charFun
  funext t
  rw [← complexMGF_mul_I hX, ← complexMGF_mul_I hY]
  exact hEq (by simpa [U] using And.intro h0X h0Y)

end
end JinWishart
#print axioms JinWishart.map_eq_of_mgf_eventuallyEq_zero
