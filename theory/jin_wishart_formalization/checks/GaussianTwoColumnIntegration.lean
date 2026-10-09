import JinWishartFormalization.GaussianTwoColumnIntegration

open MeasureTheory ProbabilityTheory JinWishart
open scoped ENNReal

#print axioms stdGaussian_sum_split
#print axioms twoColumnSplit_law
#print axioms twoColumnJoin_split
#print axioms twoColumnSplit_join
#print axioms twoColumnJoin_complex_first
#print axioms twoColumnJoin_complex_second
#print axioms twoColumnJoin_law
#print axioms twoColumn_lintegral_eq_iterated
#print axioms paperTwoColumnSpectrum_event_eq_iterated
#print axioms twoColumn_gaussian_fiber_rotation
#print axioms twoColumn_rotated_split_law

-- A real 3x2 noncentral model: an actual threshold event, not an hDensity interface.
example (M : Matrix (Fin 3) (Fin 2) ℂ) (x : ℝ) :
    ((stdGaussian (ComplexSample (m := 3) (n := 2))).map (paperJointSpectrum M))
      {y | y ⟨1, by decide⟩ < x ∧ x < y ⟨0, by decide⟩} =
      ∫⁻ u, ∫⁻ v, ((paperJointSpectrum M) ⁻¹'
        {y | y ⟨1, by decide⟩ < x ∧ x < y ⟨0, by decide⟩}).indicator (fun _ => (1 : ℝ≥0∞))
        (twoColumnJoin (u, v)) ∂stdGaussian (TwoColumnBlock 3) ∂stdGaussian (TwoColumnBlock 3) := by
  apply paperTwoColumnSpectrum_event_eq_iterated
  exact (measurableSet_lt
    (measurable_pi_apply (⟨1, by decide⟩ : Fin (min 3 2))) measurable_const).inter
    (measurableSet_lt measurable_const
      (measurable_pi_apply (⟨0, by decide⟩ : Fin (min 3 2))))

-- Zero rows are included in the product probability law.
example : (stdGaussian (ComplexSample (m := 0) (n := 2))).map twoColumnSplit =
    (stdGaussian (TwoColumnBlock 0)).prod (stdGaussian (TwoColumnBlock 0)) :=
  twoColumnSplit_law 0

-- Identity frame is a runnable example of the conditional rotation theorem.
example (m : ℕ) :
    (stdGaussian (ComplexSample (m := m) (n := 2))).map
      (fun z => ((twoColumnSplit z).1, (LinearIsometryEquiv.refl ℝ (TwoColumnBlock m))
        (twoColumnSplit z).2)) =
      (stdGaussian (TwoColumnBlock m)).prod (stdGaussian (TwoColumnBlock m)) := by
  exact twoColumn_rotated_split_law m (fun _ => LinearIsometryEquiv.refl _ _) (by fun_prop)
