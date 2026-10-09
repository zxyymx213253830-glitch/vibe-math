import JinWishartFormalization.GaussianComplexOrthogonalResidual

open MeasureTheory ProbabilityTheory JinWishart

#print axioms complexOrthogonalResidual_apply
#print axioms complexOrthogonalResidual_orthogonal
#print axioms complexOrthogonalResidual_selfAdjoint_real
#print axioms complexOrthogonalResidual_norm_sq
#print axioms stdGaussian_complex_projection_indep_residual
#print axioms indepFun_comp_complexColumnCoordinates
#print axioms actualComplexColumn_projection_indep_residual
#print axioms actualComplexColumn_projection_indep_residualEnergy
#print axioms actualComplexColumn_projection_residual_joint_law

example (a : ComplexColumnSpace 3) (ha : ‖a‖ = 1) :
    IndepFun (fun v : TwoColumnBlock 3 => inner ℂ a (actualComplexColumn v))
      (fun v => ‖complexOrthogonalResidual a (actualComplexColumn v)‖ ^ 2)
      (stdGaussian (TwoColumnBlock 3)) :=
  actualComplexColumn_projection_indep_residualEnergy a ha

example (a : ComplexColumnSpace 2) (ha : ‖a‖ = 1) (v : TwoColumnBlock 2) :
    ‖actualComplexColumn v‖ ^ 2 = ‖inner ℂ a (actualComplexColumn v)‖ ^ 2 +
      ‖complexOrthogonalResidual a (actualComplexColumn v)‖ ^ 2 :=
  complexOrthogonalResidual_norm_sq a _ ha
