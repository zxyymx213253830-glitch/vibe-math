import JinWishartFormalization.GaussianEuclideanBallDensity
import JinWishartFormalization.ThresholdNoAtom
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Group.Measure

/-!
# Actual matrix Gaussian law and spectral-event density integrals

All matrix dimensions and deterministic complex means are allowed. We
identify the shifted Gaussian density in real encoded coordinates and
express every measurable ordered-spectral event as an integral over the
original sample space. This is NOT a density on the eigenvalue space:
the Gram/spectral Jacobian and angular integration are still missing.
[需人工审查] Encoding volume, translation signs, model and event interpretation.
-/

open MeasureTheory ProbabilityTheory

namespace JinWishart

noncomputable section

/-- Full shifted Gaussian law, not merely its mass on balls. -/
theorem stdGaussian_shift_eq_withDensity {ι : Type*} [Fintype ι]
    (μ : EuclideanSpace ℝ ι) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (fun z => z + μ) =
      volume.withDensity (fun z => ENNReal.ofReal (euclideanStdGaussianDensity (z - μ))) := by
  let e : EuclideanSpace ℝ ι ≃ᵐ EuclideanSpace ℝ ι := MeasurableEquiv.addRight μ
  have hmp : MeasurePreserving e volume volume := measurePreserving_add_right volume μ
  rw [stdGaussian_euclidean_eq_radialDensity]
  have h := map_withDensity_measurePreserving e volume volume hmp
    (fun z => ENNReal.ofReal (euclideanStdGaussianDensity z)) (by
      unfold euclideanStdGaussianDensity
      fun_prop)
  simpa [e, Function.comp_def, euclideanStdGaussianDensity, sub_eq_add_neg] using h

/-- The entire ordered spectrum of the paper's small-side actual Gram matrix. -/
def paperJointSpectrum {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ)
    (z : ComplexSample (m := m) (n := n)) : Fin (min m n) → ℝ :=
  fun i => paperModelEigenvalue M i z

theorem measurable_paperJointSpectrum {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) :
    Measurable (paperJointSpectrum M) :=
  measurable_pi_iff.mpr (measurable_paperModelEigenvalue M)

theorem paperJointSpectrum_add_mean {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ)
    (z : ComplexSample (m := m) (n := n)) :
    paperJointSpectrum 0 (z + complexSampleMean M) = paperJointSpectrum M z := by
  funext i
  simp [paperJointSpectrum, paperModelEigenvalue, complexSampleMatrix_add_mean]

/-- The actual noncentral joint spectral law is the central spectral map of
the shifted Gaussian density. No candidate spectral density is assumed. -/
theorem paperJointSpectrumLaw_eq_density_pushforward {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) :
    (stdGaussian (ComplexSample (m := m) (n := n))).map (paperJointSpectrum M) =
      (volume.withDensity (fun z =>
        ENNReal.ofReal (euclideanStdGaussianDensity (z - complexSampleMean M)))).map
          (paperJointSpectrum (0 : Matrix (Fin m) (Fin n) ℂ)) := by
  rw [← stdGaussian_shift_eq_withDensity]
  rw [Measure.map_map (measurable_paperJointSpectrum _) (by fun_prop)]
  congr 1
  funext z
  exact (paperJointSpectrum_add_mean M z).symm

/-- Every Borel spectral event is an explicit integral over the encoded
Gaussian matrix sample coordinates, in any rectangular dimension. -/
theorem paperJointSpectrum_event_eq_densityIntegral {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (B : Set (Fin (min m n) → ℝ))
    (hB : MeasurableSet B) :
    ((stdGaussian (ComplexSample (m := m) (n := n))).map (paperJointSpectrum M)) B =
      ∫⁻ z in (paperJointSpectrum (0 : Matrix (Fin m) (Fin n) ℂ)) ⁻¹' B,
        ENNReal.ofReal (euclideanStdGaussianDensity (z - complexSampleMean M)) := by
  rw [paperJointSpectrumLaw_eq_density_pushforward,
    Measure.map_apply (measurable_paperJointSpectrum _) hB,
    withDensity_apply _ (hB.preimage (measurable_paperJointSpectrum _))]

end

end JinWishart
