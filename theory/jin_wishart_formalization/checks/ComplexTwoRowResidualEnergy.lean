import JinWishartFormalization.ComplexTwoRowResidualEnergy

open MeasureTheory ProbabilityTheory JinWishart

#print axioms complexTwoRowPartner_norm
#print axioms complexTwoRowPartner_residual
#print axioms complexTwoRow_residualEnergy_eq_projection
#print axioms complexGaussianEnergy_law
#print axioms complexGaussian_scaled_energy
#print axioms actualTwoRow_residualEnergy_law
#print axioms actualTwoRow_projection_residualEnergy_joint_law

-- A genuine unit direction, not an empty hypothesis.
example :
    (stdGaussian (TwoColumnBlock 2)).map
      (fun v => ‖complexOrthogonalResidual
        (EuclideanSpace.single (0 : Fin 2) (1 : ℂ)) (actualComplexColumn v)‖ ^ 2) =
      expMeasure 1 := by
  apply actualTwoRow_residualEnergy_law
  simp

example (a : ComplexColumnSpace 2) (ha : ‖a‖ = 1) :
    (stdGaussian (TwoColumnBlock 2)).map
      (fun v => (inner ℂ a (actualComplexColumn v),
        ‖complexOrthogonalResidual a (actualComplexColumn v)‖ ^ 2)) =
      ((stdGaussian ℂ).map (fun z => (Real.sqrt 2)⁻¹ • z)).prod (expMeasure 1) :=
  actualTwoRow_projection_residualEnergy_joint_law a ha

example (a z : ComplexColumnSpace 2) (ha : ‖a‖ = 1) :
    ‖z‖ ^ 2 = ‖inner ℂ a z‖ ^ 2 + ‖inner ℂ (complexTwoRowPartner a) z‖ ^ 2 := by
  rw [complexOrthogonalResidual_norm_sq a z ha,
    complexTwoRow_residualEnergy_eq_projection a z ha]
