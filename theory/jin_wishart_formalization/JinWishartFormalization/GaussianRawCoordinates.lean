import JinWishartFormalization.GaussianMatrixSpectralIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Gaussian density after nonzero scalar coordinate rescaling

The generic transport lemma retains the inverse Jacobian explicitly. It is
intended for the sqrt(2) conversion from encoded standard-real Gaussian
coordinates to raw complex real/imaginary coordinates, not a spectral Jacobian.
[需人工审查] Volume convention, scalar orientation, and model interpretation.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace JinWishart

noncomputable section

/-- Density transport for any measurable density and nonzero real scalar. -/
theorem map_withDensity_smul_euclidean {ι : Type*} [Fintype ι]
    (r : ℝ) (hr : r ≠ 0) (f : EuclideanSpace ℝ ι → ℝ≥0∞) (hf : Measurable f) :
    (volume.withDensity f).map (fun z => r • z) =
      volume.withDensity (fun z =>
        ENNReal.ofReal (abs (r ^ Fintype.card ι)⁻¹) * f (r⁻¹ • z)) := by
  let e : EuclideanSpace ℝ ι ≃ᵐ EuclideanSpace ℝ ι :=
    (Homeomorph.smul (isUnit_iff_ne_zero.mpr hr).unit).toMeasurableEquiv
  have hmp : MeasurePreserving e volume (volume.map e) :=
    ⟨e.measurable, rfl⟩
  have h := map_withDensity_measurePreserving e volume (volume.map e) hmp f hf
  have he (z : EuclideanSpace ℝ ι) : e z = r • z := rfl
  have hes (z : EuclideanSpace ℝ ι) : e.symm z = r⁻¹ • z := by
    apply e.injective
    simp only [e.apply_symm_apply, he, smul_smul, mul_inv_cancel₀ hr, one_smul]
  simp only [Function.comp_def, hes] at h
  rw [show (e : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) =
    (fun z => r • z) from funext he] at h
  rw [Measure.map_addHaar_smul volume hr, finrank_euclideanSpace,
    withDensity_smul_measure] at h
  rw [h]
  exact (withDensity_smul _ (show Measurable (fun z => f (r⁻¹ • z)) from
    hf.comp (by fun_prop))).symm

/-- The actual shifted standard Gaussian law under scalar rescaling. -/
theorem stdGaussian_scaled_shift_eq_withDensity {ι : Type*} [Fintype ι]
    (r : ℝ) (hr : r ≠ 0) (μ : EuclideanSpace ℝ ι) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (fun z => r • (z + μ)) =
      volume.withDensity (fun z => ENNReal.ofReal (abs (r ^ Fintype.card ι)⁻¹) *
        ENNReal.ofReal (euclideanStdGaussianDensity (r⁻¹ • z - μ))) := by
  rw [← map_withDensity_smul_euclidean r hr
    (fun z => ENNReal.ofReal (euclideanStdGaussianDensity (z - μ))) (by
    unfold euclideanStdGaussianDensity
    fun_prop), ← stdGaussian_shift_eq_withDensity]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- The even-dimensional inverse Jacobian and standard density simplify to
the conventional complex Gaussian constant `pi^(-k)`. -/
theorem sqrtTwo_scaled_density {ι : Type*} [Fintype ι] (k : ℕ)
    (hcard : Fintype.card ι = 2 * k) (z ν : EuclideanSpace ℝ ι) :
    abs (((Real.sqrt 2)⁻¹) ^ Fintype.card ι)⁻¹ *
        euclideanStdGaussianDensity (Real.sqrt 2 • z - Real.sqrt 2 • ν) =
      (Real.pi⁻¹) ^ k * Real.exp (-‖z - ν‖ ^ 2) := by
  have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsp : (0 : ℝ) < Real.sqrt (2 * Real.pi) :=
    Real.sqrt_pos.mpr (by positivity)
  have hn : ‖Real.sqrt 2 • z - Real.sqrt 2 • ν‖ ^ 2 = 2 * ‖z - ν‖ ^ 2 := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hs, mul_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hc : abs (((Real.sqrt 2)⁻¹) ^ (2 * k))⁻¹ *
      (Real.sqrt (2 * Real.pi))⁻¹ ^ (2 * k) = (Real.pi⁻¹) ^ k := by
    rw [abs_of_pos (inv_pos.mpr (pow_pos (inv_pos.mpr hs) _)), ← inv_pow, inv_inv,
      pow_mul, pow_mul, inv_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
      ← mul_pow]
    congr 1
    field_simp
  unfold euclideanStdGaussianDensity
  rw [hcard, hn, ← mul_assoc, hc]
  congr 2
  ring

/-- Raw real/imaginary coordinates have independent variance-one-half
Gaussian density; the theorem identifies the actual law, not a candidate. -/
theorem stdGaussian_halfVariance_shift_eq_withDensity {ι : Type*} [Fintype ι]
    (k : ℕ) (hcard : Fintype.card ι = 2 * k) (ν : EuclideanSpace ℝ ι) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (fun z => (Real.sqrt 2)⁻¹ • z + ν) =
      volume.withDensity (fun z => ENNReal.ofReal
        ((Real.pi⁻¹) ^ k * Real.exp (-‖z - ν‖ ^ 2))) := by
  have hs : (Real.sqrt (2 : ℝ)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have h := stdGaussian_scaled_shift_eq_withDensity (Real.sqrt 2)⁻¹
    (inv_ne_zero hs) (Real.sqrt 2 • ν)
  have hfun : (fun z : EuclideanSpace ℝ ι =>
      (Real.sqrt 2)⁻¹ • (z + Real.sqrt 2 • ν)) =
      (fun z => (Real.sqrt 2)⁻¹ • z + ν) := by
    funext z
    simp only [smul_add, smul_smul, inv_mul_cancel₀ hs, one_smul]
  rw [hfun] at h
  rw [h]
  congr 1
  funext z
  rw [← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  simpa only [inv_inv] using sqrtTwo_scaled_density k hcard z ν

/-- Raw matrix coordinates carry no sqrt(2) multiplier on the mean. -/
def rawComplexSampleMean {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) :
    ComplexSample (m := m) (n := n) := (Real.sqrt 2)⁻¹ • complexSampleMean M

theorem rawComplexSampleMean_apply {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ)
    (ij : (Fin m × Fin n) × Fin 2) :
    rawComplexSampleMean M ij =
      if ij.2 = 0 then (M ij.1.1 ij.1.2).re else (M ij.1.1 ij.1.2).im := by
  have hs : (Real.sqrt (2 : ℝ)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  simp [rawComplexSampleMean, complexSampleMean, hs]

/-- Restoring the encoded sqrt(2) produces exactly the raw complex entry. -/
theorem complexSampleMatrix_sqrtTwo_smul {m n : ℕ}
    (z : ComplexSample (m := m) (n := n)) (i : Fin m) (j : Fin n) :
    complexSampleMatrix (Real.sqrt 2 • z) i j =
      (z ((i, j), 0) : ℂ) + Complex.I * z ((i, j), 1) := by
  apply Complex.ext <;> simp [complexSampleMatrix]

theorem rawComplexSample_norm_sq_eq_frobenius {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (z : ComplexSample (m := m) (n := n)) :
    ‖z - rawComplexSampleMean M‖ ^ 2 =
      ∑ i : Fin m, ∑ j : Fin n, ‖complexSampleMatrix (Real.sqrt 2 • z) i j - M i j‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, PiLp.sub_apply,
    rawComplexSampleMean_apply,
    complexSampleMatrix_sqrtTwo_smul, Complex.sq_norm, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im]
  simp [pow_two]

/-- Density in raw real/imaginary coordinates, valid in any rectangular dimension. -/
def rawComplexGaussianDensity {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ)
    (z : ComplexSample (m := m) (n := n)) : ℝ :=
  (Real.pi⁻¹) ^ (m * n) * Real.exp (-‖z - rawComplexSampleMean M‖ ^ 2)

theorem rawComplexGaussianDensity_eq_frobenius {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (z : ComplexSample (m := m) (n := n)) :
    rawComplexGaussianDensity M z = (Real.pi⁻¹) ^ (m * n) *
      Real.exp (-(∑ i : Fin m, ∑ j : Fin n,
        ‖complexSampleMatrix (Real.sqrt 2 • z) i j - M i j‖ ^ 2)) := by
  rw [rawComplexGaussianDensity, rawComplexSample_norm_sq_eq_frobenius]

theorem rawComplexSampleLaw_eq_withDensity {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) :
    (stdGaussian (ComplexSample (m := m) (n := n))).map
        (fun z => (Real.sqrt 2)⁻¹ • z + rawComplexSampleMean M) =
      volume.withDensity (fun z => ENNReal.ofReal (rawComplexGaussianDensity M z)) := by
  apply stdGaussian_halfVariance_shift_eq_withDensity (m * n)
  simp only [Fintype.card_prod, Fintype.card_fin]
  omega

/-- The ordered spectrum as a function of unscaled raw matrix coordinates. -/
def paperRawJointSpectrum {m n : ℕ} (z : ComplexSample (m := m) (n := n)) :
    Fin (min m n) → ℝ :=
  paperJointSpectrum (0 : Matrix (Fin m) (Fin n) ℂ) (Real.sqrt 2 • z)

theorem measurable_paperRawJointSpectrum {m n : ℕ} :
    Measurable (paperRawJointSpectrum (m := m) (n := n)) :=
  (measurable_paperJointSpectrum _).comp (by fun_prop)

theorem paperRawJointSpectrum_sample_eq {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ)
    (z : ComplexSample (m := m) (n := n)) :
    paperRawJointSpectrum ((Real.sqrt 2)⁻¹ • z + rawComplexSampleMean M) =
      paperJointSpectrum M z := by
  have hs : (Real.sqrt (2 : ℝ)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  unfold paperRawJointSpectrum rawComplexSampleMean
  simp only [smul_add, smul_smul, mul_inv_cancel₀ hs, one_smul]
  exact paperJointSpectrum_add_mean M z

/-- An actual spectral event integrated against the standard complex Gaussian
matrix density in raw coordinates. Still not a density on spectral space. -/
theorem paperJointSpectrum_event_eq_rawDensityIntegral {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (B : Set (Fin (min m n) → ℝ))
    (hB : MeasurableSet B) :
    ((stdGaussian (ComplexSample (m := m) (n := n))).map (paperJointSpectrum M)) B =
      ∫⁻ z in (paperRawJointSpectrum (m := m) (n := n)) ⁻¹' B,
        ENNReal.ofReal (rawComplexGaussianDensity M z) := by
  have hlaw : (stdGaussian (ComplexSample (m := m) (n := n))).map (paperJointSpectrum M) =
      (volume.withDensity (fun z => ENNReal.ofReal (rawComplexGaussianDensity M z))).map
        paperRawJointSpectrum := by
    rw [← rawComplexSampleLaw_eq_withDensity M,
      Measure.map_map measurable_paperRawJointSpectrum (by fun_prop)]
    congr 1
    funext z
    exact (paperRawJointSpectrum_sample_eq M z).symm
  rw [hlaw, Measure.map_apply measurable_paperRawJointSpectrum hB,
    withDensity_apply _ (hB.preimage measurable_paperRawJointSpectrum)]

end

end JinWishart
