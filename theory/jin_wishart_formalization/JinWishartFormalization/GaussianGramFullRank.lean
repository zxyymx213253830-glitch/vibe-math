import JinWishartFormalization.ComplexGramSimpleSpectrum
import JinWishartFormalization.GaussianGramDimensions

/-!
# Full column rank of actual shifted complex Gaussian matrices

Codex proofs, reusing the existing generic Gram encoding, diagonal witness and
nonzero-polynomial Gaussian null-set theorem. No new density hypothesis, QR
basis selection or radial integration is introduced.

The column-Gram assertions require n <= m, include n=0, and allow any fixed
complex mean. General Wishart matrix and spectral densities are separate.
[需人工审查] Inherited polynomial null-set/Fubini argument, Gaussian absolute
continuity, real coordinate encoding and its variance convention.
-/

open Matrix MeasureTheory ProbabilityTheory
open scoped ComplexOrder
namespace JinWishart
noncomputable section
variable {m n : ℕ}

theorem genericComplexGram_det_eval (z : ComplexSample (m := m) (n := n)) :
    sampleEval z (genericComplexGram m n).det =
      (complexGram (complexSampleMatrix z)).det := by
  rw [RingHom.map_det]
  change ((genericComplexGram m n).map (sampleEval z)).det = _
  rw [genericComplexGram_map]

theorem complexGram_witnessMean_det_ne_zero (hnm : n ≤ m) :
    (complexGram (witnessMean hnm)).det ≠ 0 := by
  rw [complexGram_witnessMean, Matrix.det_diagonal]
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact_mod_cast (show (((j : ℕ) : ℝ) + 1) ^ 2 ≠ 0 by positivity)

theorem genericComplexGram_det_ne_zero (hnm : n ≤ m) :
    (genericComplexGram m n).det ≠ 0 := by
  intro hzero
  have h := genericComplexGram_det_eval (complexSampleMean (witnessMean hnm))
  rw [hzero, map_zero, complexSampleMatrix_complexSampleMean] at h
  exact complexGram_witnessMean_det_ne_zero hnm h.symm

/-- Actual noncentral Gaussian column Gram is nonsingular almost surely. -/
theorem complexSample_shiftedGram_det_ne_zero_ae (hnm : n ≤ m)
    (M : Matrix (Fin m) (Fin n) ℂ) :
    ∀ᵐ z ∂stdGaussian (ComplexSample (m := m) (n := n)),
      (complexGram (complexSampleMatrix z + M)).det ≠ 0 := by
  have h := sampleEval_ne_zero_ae (genericComplexGram_det_ne_zero hnm) M
  filter_upwards [h] with z hz
  rwa [genericComplexGram_det_eval, complexSampleMatrix_add_mean] at hz

theorem complexSample_shiftedGram_isUnit_det_ae (hnm : n ≤ m)
    (M : Matrix (Fin m) (Fin n) ℂ) :
    ∀ᵐ z ∂stdGaussian (ComplexSample (m := m) (n := n)),
      IsUnit (complexGram (complexSampleMatrix z + M)).det := by
  filter_upwards [complexSample_shiftedGram_det_ne_zero_ae hnm M] with z hz
  exact isUnit_iff_ne_zero.mpr hz

/-- PSD becomes strictly positive definite after the actual null-set proof. -/
theorem complexSample_shiftedGram_posDef_ae (hnm : n ≤ m)
    (M : Matrix (Fin m) (Fin n) ℂ) :
    ∀ᵐ z ∂stdGaussian (ComplexSample (m := m) (n := n)),
      (complexGram (complexSampleMatrix z + M)).PosDef := by
  filter_upwards [complexSample_shiftedGram_det_ne_zero_ae hnm M] with z hz
  exact (complexGram_posSemidef _).posDef_iff_det_ne_zero.mpr hz

theorem complexSample_shiftedColumnMap_injective_ae (hnm : n ≤ m)
    (M : Matrix (Fin m) (Fin n) ℂ) :
    ∀ᵐ z ∂stdGaussian (ComplexSample (m := m) (n := n)),
      Function.Injective (complexSampleMatrix z + M).toEuclideanLin := by
  filter_upwards [complexSample_shiftedGram_isUnit_det_ae hnm M] with z hz
  exact gramColumnMap_injective _ hz

theorem complexSample_shiftedColumnSpace_finrank_real_ae (hnm : n ≤ m)
    (M : Matrix (Fin m) (Fin n) ℂ) :
    ∀ᵐ z ∂stdGaussian (ComplexSample (m := m) (n := n)),
      Module.finrank ℝ (totalGramColumnSpaceReal (complexSampleMatrix z + M)) = 2 * n := by
  filter_upwards [complexSample_shiftedGram_isUnit_det_ae hnm M] with z hz
  exact totalGramColumnSpaceReal_finrank _ hz

theorem complexSample_shiftedColumnSpace_orthogonal_finrank_ae (hnm : n ≤ m)
    (M : Matrix (Fin m) (Fin n) ℂ) :
    ∀ᵐ z ∂stdGaussian (ComplexSample (m := m) (n := n)),
      Module.finrank ℝ (totalGramColumnSpaceReal (complexSampleMatrix z + M))ᗮ =
        2 * (m - n) := by
  filter_upwards [complexSample_shiftedGram_isUnit_det_ae hnm M] with z hz
  exact totalGramColumnSpaceReal_orthogonal_finrank _ hz

end
end JinWishart

#print axioms JinWishart.genericComplexGram_det_eval
#print axioms JinWishart.complexGram_witnessMean_det_ne_zero
#print axioms JinWishart.genericComplexGram_det_ne_zero
#print axioms JinWishart.complexSample_shiftedGram_det_ne_zero_ae
#print axioms JinWishart.complexSample_shiftedGram_isUnit_det_ae
#print axioms JinWishart.complexSample_shiftedGram_posDef_ae
#print axioms JinWishart.complexSample_shiftedColumnMap_injective_ae
#print axioms JinWishart.complexSample_shiftedColumnSpace_finrank_real_ae
#print axioms JinWishart.complexSample_shiftedColumnSpace_orthogonal_finrank_ae
