import JinWishartFormalization.GaussianRawCoordinates

open MeasureTheory ProbabilityTheory JinWishart

#print axioms map_withDensity_smul_euclidean
#print axioms stdGaussian_scaled_shift_eq_withDensity
#print axioms sqrtTwo_scaled_density
#print axioms stdGaussian_halfVariance_shift_eq_withDensity
#print axioms rawComplexSampleMean_apply
#print axioms complexSampleMatrix_sqrtTwo_smul
#print axioms rawComplexSample_norm_sq_eq_frobenius
#print axioms rawComplexGaussianDensity_eq_frobenius
#print axioms rawComplexSampleLaw_eq_withDensity
#print axioms paperRawJointSpectrum_sample_eq
#print axioms paperJointSpectrum_event_eq_rawDensityIntegral

-- Probability normalization follows from the actual Gaussian law, not an assumption.
example {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) :
    ∫⁻ z : ComplexSample (m := m) (n := n),
      ENNReal.ofReal (rawComplexGaussianDensity M z) = 1 := by
  have h := paperJointSpectrum_event_eq_rawDensityIntegral M Set.univ MeasurableSet.univ
  rw [Measure.map_apply (measurable_paperJointSpectrum M) MeasurableSet.univ] at h
  simpa using h.symm

-- A concrete multi-eigenvalue event on the rectangular actual noncentral model.
example (M : Matrix (Fin 3) (Fin 2) ℂ) (x : ℝ) :
    ((stdGaussian (ComplexSample (m := 3) (n := 2))).map (paperJointSpectrum M))
      {y | y ⟨1, by decide⟩ < x ∧ x < y ⟨0, by decide⟩} =
      ∫⁻ z in (paperRawJointSpectrum (m := 3) (n := 2)) ⁻¹'
        {y | y ⟨1, by decide⟩ < x ∧ x < y ⟨0, by decide⟩},
        ENNReal.ofReal (rawComplexGaussianDensity M z) := by
  apply paperJointSpectrum_event_eq_rawDensityIntegral
  exact (measurableSet_lt
    (measurable_pi_apply (⟨1, by decide⟩ : Fin (min 3 2))) measurable_const).inter
    (measurableSet_lt measurable_const
      (measurable_pi_apply (⟨0, by decide⟩ : Fin (min 3 2))))

-- Empty dimensions retain probability mass one.
example : rawComplexGaussianDensity (0 : Matrix (Fin 0) (Fin 2) ℂ) 0 = 1 := by
  simp [rawComplexGaussianDensity, rawComplexSampleMean, complexSampleMean]
  rfl
