import JinWishartFormalization.WishartProbability

/-!
# Deterministic scalar scattering-scale normalization

The Lean probability model uses unit complex noise variance.  This module
records the pointwise algebra needed to convert a physical scalar channel
`H = μ + ε Z` to that normalization.  It does not identify the paper's
global MIMO covariance model or SNR parameters.
-/

namespace JinWishart

/-- Energy of a physical scalar channel after division by the scattering
variance `ε²`. -/
noncomputable def physicalScalarNormalizedEnergy
    (μ : ℂ) (ε : ℝ) (z : ComplexSample (m := 1) (n := 1)) : ℝ :=
  ‖μ + (ε : ℂ) * complexSampleMatrix z 0 0‖ ^ 2 / ε ^ 2

/-- Normalizing a scalar channel with positive scattering scale `ε` is
equivalent pointwise to unit-variance noise with mean `μ/ε`. -/
theorem physicalScalarNormalizedEnergy_eq_unitVarianceMean
    (μ : ℂ) (ε : ℝ) (hε : 0 < ε)
    (z : ComplexSample (m := 1) (n := 1)) :
    physicalScalarNormalizedEnergy μ ε z =
      ‖complexSampleMatrix z 0 0 + μ / (ε : ℂ)‖ ^ 2 := by
  have hε0 : ε ≠ 0 := ne_of_gt hε
  have hεC : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε0
  have hfactor : μ + (ε : ℂ) * complexSampleMatrix z 0 0 =
      (ε : ℂ) * (complexSampleMatrix z 0 0 + μ / (ε : ℂ)) := by
    field_simp [hεC]
    ring
  unfold physicalScalarNormalizedEnergy
  rw [hfactor, norm_mul, Complex.norm_real]
  rw [Real.norm_eq_abs, abs_of_pos hε]
  field_simp [hε0]

end JinWishart
