import JinWishartFormalization.LogMomentIntegrability
import JinWishartFormalization.NoncentralInverseMinimumRealMoments
import JinWishartFormalization.CentralWishartTraceLaw
import JinWishartFormalization.WeylComplexHermitian
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-! Finite trace, eigenvalue and absolute logarithmic moments of actual Gram samples.
Codex. Fixed arbitrary mean, every m>=N>0 including square samples.
[需人工审查] Inherited Gaussian normalization, spectral and AE interpretation.
-/
open Matrix MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

theorem measurable_actualNoncentralEigenvalue {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (i : Fin (Fintype.card (Fin n))) :
    Measurable (complexNoncentralSampleEigenvalue M i) := by
  exact (measurable_pi_iff.mp
    (measurable_complexNoncentralSampleEigenvalueVector_of_continuous M
      (orderedHermitianEigenvalueCoordinatesContinuous n))) i

theorem integrable_actualNoncentralGram_trace {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) :
    Integrable (fun z : ComplexSample (m := m) (n := n) =>
      (complexGram (complexSampleMatrix z+M)).trace.re) (stdGaussian _) := by
  have hid : MemLp (id : ComplexSample (m := m) (n := n) → ComplexSample)
      2 (stdGaussian _) := IsGaussian.memLp_two_id
  have hc : MemLp (fun _ : ComplexSample (m := m) (n := n) => complexSampleMean M)
      2 (stdGaussian _) := memLp_const _
  have hlp : MemLp (fun z : ComplexSample (m := m) (n := n) => z+complexSampleMean M)
      2 (stdGaussian _) := hid.add hc
  have hi := hlp.integrable_norm_pow' (p := 2)
  have he (z : ComplexSample (m := m) (n := n)) :
      (complexGram (complexSampleMatrix z+M)).trace.re = ‖z+complexSampleMean M‖^2/2 := by
    have h := complexSampleGram_trace_half_norm (z+complexSampleMean M)
    simpa only [complexSampleGram,complexSampleMatrix_add_mean] using h
  simp_rw [he]
  exact hi.div_const 2

theorem actualNoncentralEigenvalue_le_trace {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (i : Fin (Fintype.card (Fin n)))
    (z : ComplexSample (m := m) (n := n)) :
    complexNoncentralSampleEigenvalue M i z ≤
      (complexGram (complexSampleMatrix z+M)).trace.re := by
  classical
  let h := (complexGram_posSemidef (complexSampleMatrix z+M)).1
  let e : Fin (Fintype.card (Fin n)) ≃ Fin n :=
    Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))
  have hs : (∑ j, h.eigenvalues₀ j) = ∑ j, h.eigenvalues j := by
    simpa only [Matrix.IsHermitian.eigenvalues,e,Equiv.symm_apply_apply] using
      (Equiv.sum_comp e (fun j => h.eigenvalues j))
  have ht := congrArg Complex.re h.trace_eq_sum_eigenvalues
  simp only [Complex.re_sum] at ht
  change (complexGram (complexSampleMatrix z+M)).trace.re = ∑ j, h.eigenvalues j at ht
  rw [← hs] at ht
  rw [ht]
  exact Finset.single_le_sum (fun j _ => complexNoncentralSampleEigenvalue_nonneg M j z)
    (Finset.mem_univ i)

theorem actualNoncentralMinimum_le_eigenvalue {m n : ℕ} (hn : 0 < n)
    (M : Matrix (Fin m) (Fin n) ℂ) (i : Fin (Fintype.card (Fin n)))
    (z : ComplexSample (m := m) (n := n)) :
    complexNoncentralSampleSmallestEigenvalue M hn z ≤ complexNoncentralSampleEigenvalue M i z := by
  exact complexNoncentralSampleEigenvalue_antitone M z
    (show i ≤ smallestEigenvalue₀Index hn by
      apply Fin.le_iff_val_le_val.mpr
      have hi := i.isLt
      simp only [Fintype.card_fin] at hi
      simp only [smallestEigenvalue₀Index,Fin.val_cast,Fin.val_last,Fintype.card_fin]
      omega)

theorem integrable_actualNoncentralEigenvalue {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (i : Fin (Fintype.card (Fin n))) :
    Integrable (complexNoncentralSampleEigenvalue M i) (stdGaussian _) := by
  apply (integrable_actualNoncentralGram_trace M).mono'
    (measurable_actualNoncentralEigenvalue M i).aestronglyMeasurable
  exact ae_of_all _ (fun z => by
    rw [Real.norm_eq_abs,abs_of_nonneg (complexNoncentralSampleEigenvalue_nonneg M i z)]
    exact actualNoncentralEigenvalue_le_trace M i z)

theorem integrable_actualNoncentral_logEigenvalue {m n : ℕ} (hn : 0 < n) (hnm : n ≤ m)
    (M : Matrix (Fin m) (Fin n) ℂ) (i : Fin (Fintype.card (Fin n))) :
    Integrable (fun z => Real.log (complexNoncentralSampleEigenvalue M i z)) (stdGaussian _) := by
  have hpos := actualNoncentral_minimum_pos_ae hn hnm M
  have hmin := (actualNoncentralRectangular_inverseMinimum_realMoment_integrable_iff
    m n hn hnm M (1/2) (by norm_num)).mpr (by
      have : (1 : ℝ) ≤ ((m-n+1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ m-n+1 by omega)
      linarith)
  refine integrable_log_of_integrable_inverse_rpow _ _
    (integrable_actualNoncentralEigenvalue M i) ?_ (1/2) (by norm_num) ?_
  · filter_upwards [hpos] with z hz
    exact hz.trans_le (actualNoncentralMinimum_le_eigenvalue hn M i z)
  · apply hmin.mono'
      (((measurable_actualNoncentralEigenvalue M i).inv).pow_const (1/2 : ℝ)).aestronglyMeasurable
    filter_upwards [hpos] with z hz
    have hnonneg := inv_nonneg.mpr (complexNoncentralSampleEigenvalue_nonneg M i z)
    change ‖(complexNoncentralSampleEigenvalue M i z)⁻¹ ^ (1/2 : ℝ)‖ ≤
      (complexNoncentralSampleSmallestEigenvalue M hn z)⁻¹ ^ (1/2 : ℝ)
    rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hnonneg _)]
    apply Real.rpow_le_rpow hnonneg _ (by norm_num)
    exact inv_anti₀ hz (actualNoncentralMinimum_le_eigenvalue hn M i z)

end
end JinWishart
#print axioms JinWishart.measurable_actualNoncentralEigenvalue
#print axioms JinWishart.integrable_actualNoncentralGram_trace
#print axioms JinWishart.actualNoncentralEigenvalue_le_trace
#print axioms JinWishart.actualNoncentralMinimum_le_eigenvalue
#print axioms JinWishart.integrable_actualNoncentralEigenvalue
#print axioms JinWishart.integrable_actualNoncentral_logEigenvalue
