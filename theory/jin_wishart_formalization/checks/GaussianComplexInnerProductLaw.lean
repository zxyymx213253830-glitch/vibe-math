import JinWishartFormalization.GaussianComplexInnerProductLaw

open MeasureTheory ProbabilityTheory JinWishart

#print axioms complexColumn_real_inner
#print axioms real_inner_complex_inner
#print axioms charFun_stdGaussian_complex_inner
#print axioms stdGaussian_complex_inner_law
#print axioms actualComplexColumn_inner_law
#print axioms twoColumnGram_offDiagonal_fixed_first_law

-- A genuine three-row/two-column Gram entry, not a one-column CDF.
example (u : TwoColumnBlock 3) :
    (stdGaussian (TwoColumnBlock 3)).map
      (fun v => complexGram (complexSampleMatrix (twoColumnJoin (u, v))) 0 1) =
      (stdGaussian ℂ).map (fun z => ((Real.sqrt 2)⁻¹ * ‖actualComplexColumn u‖) • z) :=
  twoColumnGram_offDiagonal_fixed_first_law u

-- No nonzero-vector hypothesis: the degenerate fiber is included.
example (m : ℕ) :
    (stdGaussian (TwoColumnBlock m)).map
      (fun v => inner ℂ (0 : ComplexColumnSpace m) (actualComplexColumn v)) =
      (stdGaussian ℂ).map (fun z => (0 : ℝ) • z) := by
  simpa using actualComplexColumn_inner_law (0 : ComplexColumnSpace m)

-- Real and complex inner products are compared for the actual space instances.
example (a z : ComplexColumnSpace 2) : inner ℝ a z = (inner ℂ a z).re :=
  complexColumn_real_inner a z
