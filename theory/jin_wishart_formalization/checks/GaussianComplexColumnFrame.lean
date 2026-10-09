import JinWishartFormalization.GaussianComplexColumnFrame

open MeasureTheory ProbabilityTheory JinWishart

#print axioms complexColumnCoordinates_apply
#print axioms complexColumnCoordinates_join_first
#print axioms complexColumnCoordinates_join_second
#print axioms complexColumnCoordinates_encodedFrame
#print axioms complexFrame_inner_preserved
#print axioms encodedComplexFrame_gaussianLaw
#print axioms twoColumn_complex_fiber_frame_law
#print axioms complexColumnPair_gram_entry
#print axioms complexColumnPair_gram_unitary
#print axioms actualComplexColumn_encodedFrame
#print axioms twoColumnJoin_matrix_eq_columnPair
#print axioms twoColumn_actualGram_unitary

-- Two columns, not a one-column CDF, and a genuinely complex linear frame.
example (U : ComplexColumnSpace 3 ≃ₗᵢ[ℂ] ComplexColumnSpace 3)
    (u v : TwoColumnBlock 3) :
    complexGram (complexSampleMatrix
      (twoColumnJoin (encodedComplexFrame U u, encodedComplexFrame U v))) =
      complexGram (complexSampleMatrix (twoColumnJoin (u, v))) :=
  twoColumn_actualGram_unitary U u v

-- Fixed complex frame is a non-degenerate special case of the fiber law.
example (U : ComplexColumnSpace 2 ≃ₗᵢ[ℂ] ComplexColumnSpace 2) :
    (stdGaussian (ComplexSample (m := 2) (n := 2))).map
      (fun z => ((twoColumnSplit z).1, encodedComplexFrame U (twoColumnSplit z).2)) =
      (stdGaussian (TwoColumnBlock 2)).prod (stdGaussian (TwoColumnBlock 2)) := by
  exact twoColumn_complex_fiber_frame_law 2 (fun _ => U)
    (U.continuous.measurable.comp measurable_snd)
