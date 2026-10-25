import JinWishartFormalization.LocalMGFLawUniqueness

/-! Codex. Seed 2026102508 controls precede source.
[需人工审查] Scalar analytic uniqueness and separation by the complete real dual.
This identifies finite Borel measures from ALL continuous linear projections,
not from coordinate marginals or finitely many moments. -/
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace JinWishart
noncomputable section

theorem eq_of_localMGF_all_dual
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {μ ν : Measure E} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ L : E →L[ℝ] ℝ, 0 ∈ interior (integrableExpSet L μ))
    (hν : ∀ L : E →L[ℝ] ℝ, 0 ∈ interior (integrableExpSet L ν))
    (hmgf : ∀ L : E →L[ℝ] ℝ, mgf L μ =ᶠ[𝓝 0] mgf L ν) : μ = ν := by
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one]
  exact congrArg (fun ρ : Measure ℝ => charFun ρ 1)
    (map_eq_of_mgf_eventuallyEq_zero L.continuous.measurable.aemeasurable
      L.continuous.measurable.aemeasurable (hμ L) (hν L) (hmgf L))

end
end JinWishart
#print axioms JinWishart.eq_of_localMGF_all_dual
