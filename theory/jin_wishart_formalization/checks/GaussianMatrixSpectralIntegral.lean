import JinWishartFormalization.GaussianMatrixSpectralIntegral

open MeasureTheory ProbabilityTheory JinWishart

#print axioms map_withDensity_measurePreserving
#print axioms stdGaussian_shift_eq_withDensity
#print axioms paperJointSpectrumLaw_eq_density_pushforward
#print axioms paperJointSpectrum_event_eq_densityIntegral

-- A concrete T3 two-eigenvalue crossing event, on the actual noncentral 2x2 model.
example (M : Matrix (Fin 2) (Fin 2) ℂ) (x : ℝ) :
    ((stdGaussian (ComplexSample (m := 2) (n := 2))).map (paperJointSpectrum M))
      {y | y ⟨1, by decide⟩ < x ∧ x < y ⟨0, by decide⟩} =
      ∫⁻ z in (paperJointSpectrum (0 : Matrix (Fin 2) (Fin 2) ℂ)) ⁻¹'
        {y | y ⟨1, by decide⟩ < x ∧ x < y ⟨0, by decide⟩},
        ENNReal.ofReal (euclideanStdGaussianDensity (z - complexSampleMean M)) := by
  apply paperJointSpectrum_event_eq_densityIntegral
  exact (measurableSet_lt
    (measurable_pi_apply (⟨1, by decide⟩ : Fin (min 2 2))) measurable_const).inter
    (measurableSet_lt measurable_const
      (measurable_pi_apply (⟨0, by decide⟩ : Fin (min 2 2))))

-- Normalization on the whole spectral space, including arbitrary rectangular dimensions.
example {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) :
    ∫⁻ z : ComplexSample (m := m) (n := n),
      ENNReal.ofReal (euclideanStdGaussianDensity (z - complexSampleMean M)) = 1 := by
  have h := paperJointSpectrum_event_eq_densityIntegral M Set.univ MeasurableSet.univ
  rw [Measure.map_apply (measurable_paperJointSpectrum M) MeasurableSet.univ] at h
  simpa using h.symm
