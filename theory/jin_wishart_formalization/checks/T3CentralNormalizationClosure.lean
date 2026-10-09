import JinWishartFormalization.T3CentralNormalizationClosure
import JinWishartFormalization.GaussianMatrixSpectralIntegral

open JinWishart MeasureTheory ProbabilityTheory

#print axioms sum_powerset_card_one
#print axioms theorem3CentralTwoThreeCandidate_eq_mixedRowSum
#print axioms theorem3CentralTwoThreeCandidate_gt_one
#print axioms theorem3CentralTwoThreeCandidate_ne_eventProbability

-- General helper, not limited to two rows or complex coefficients.
example (f : Finset (Fin 4) → ℝ) :
    (∑ S ∈ (Finset.univ : Finset (Fin 4)).powerset,
      if S.card = 1 then f S else 0) = ∑ i : Fin 4, f {i} := by
  exact sum_powerset_card_one _ _

-- The transcribed T3 candidate differs from the actual central 3x2 crossing event.
-- The density on eigenvalue space is NOT assumed in this test.
example :
    (theorem3IncrementCandidate 2 3 0 2 (by decide) (by decide)
      emptyNoncentralSpectrum 2).re ≠
    (stdGaussian (ComplexSample (m := 3) (n := 2))).real
      ((paperJointSpectrum (0 : Matrix (Fin 3) (Fin 2) ℂ)) ⁻¹'
        {y | y ⟨1, by decide⟩ < 2 ∧ 2 < y ⟨0, by decide⟩}) := by
  exact theorem3CentralTwoThreeCandidate_ne_eventProbability _ _
