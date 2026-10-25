import JinWishartFormalization.PSDMatrixLaplaceUniqueness
import JinWishartFormalization.ActualNoncentralMatrixLaplace

/-! Codex. Seed2026102509 controls precede source.
[需人工审查] Actual properCN1 model and candidate support/transform hypotheses.
This is a characterization, NOT a proof of an unverified candidate density. -/
open Matrix MeasureTheory ProbabilityTheory
open scoped ComplexOrder
namespace JinWishart
noncomputable section

theorem noncentralWishart_eq_of_PSD_matrixLaplace {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ)
    {ν : Measure (Matrix (Fin n) (Fin n) ℂ)} [IsFiniteMeasure ν]
    (hν : ∀ᵐ W ∂ν, W.PosSemidef)
    (hLaplace : ∀ T : Matrix (Fin n) (Fin n) ℂ, T.PosSemidef →
      (∫ W, Real.exp (-(T * W).trace.re) ∂ν) =
        (‖(1 + T).det‖ ^ m)⁻¹ * Real.exp (-(M * T * (1 + T)⁻¹ * Mᴴ).trace.re)) :
    ν = complexNoncentralWishart M := by
  have hactual : ∀ᵐ W ∂complexNoncentralWishart M, W.PosSemidef :=
    (mem_ae_iff_prob_eq_one Matrix.posSemidef_is_closed.measurableSet).mpr
      (complexNoncentralWishart_measure_posSemidef M)
  apply finite_PSD_measures_eq_of_matrixLaplace hν hactual
  intro T hT
  exact (hLaplace T hT).trans (noncentralWishart_PSD_matrixLaplace M T hT).symm

end
end JinWishart
#print axioms JinWishart.noncentralWishart_eq_of_PSD_matrixLaplace
