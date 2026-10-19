import JinWishartFormalization.GramMinimumColumnComparison
import JinWishartFormalization.NoncentralMinimumDiversity

/-!
# Actual minimum with a fixed invertible column covariance factor

The physical sample is Z B + M, not (Z+M) B. Its row covariance is B* B.
The normalized mean is M B^-1 and is fixed. Codex.
[需人工审查] Matrix measurability, covariance orientation and spectral model.
-/
open Matrix Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace JinWishart
noncomputable section

theorem measurable_gramSmallestValue {m n : ℕ} (hn : 0<n) :
    Measurable (fun A : Matrix (Fin m) (Fin n) ℂ => gramSmallestValue A hn) := by
  apply measurable_of_Iio
  intro x
  have he : (fun A : Matrix (Fin m) (Fin n) ℂ => gramSmallestValue A hn) ⁻¹' Set.Iio x =
      (fun A => complexGram A) ⁻¹' (smallestEigenvalueTailEvent x)ᶜ := by
    ext A
    have hs := smallestEigenvalueTailEvent_iff_smallest_eigenvalue₀_ge
      (complexGram A) (complexGram_posSemidef A).1 (by simpa using hn) x
    change gramSmallestValue A hn < x ↔ complexGram A ∉ smallestEigenvalueTailEvent x
    rw [hs]
    exact lt_iff_not_ge
  rw [he]
  apply (measurableSet_smallestEigenvalueTailEvent x).compl.preimage
  apply Measurable.of_eval_matrix
  intro i j
  simp only [complexGram,Matrix.mul_apply,Matrix.conjTranspose_apply]
  fun_prop

def correlatedColumnMinimum {m n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (M : Matrix (Fin m) (Fin n) ℂ) (hn : 0<n) (z : ComplexSample (m := m) (n := n)) : ℝ :=
  gramSmallestValue (complexSampleMatrix z*B+M) hn

theorem measurable_correlatedColumnMinimum {m n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (M : Matrix (Fin m) (Fin n) ℂ) (hn : 0<n) :
    Measurable (correlatedColumnMinimum B M hn) := by
  apply (measurable_gramSmallestValue hn).comp
  apply Measurable.of_eval_matrix
  intro i j
  simp only [Matrix.add_apply,Matrix.mul_apply,complexSampleMatrix]
  fun_prop

theorem correlatedColumn_sample_identity {m n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (M : Matrix (Fin m) (Fin n) ℂ) (hB : IsUnit B.det)
    (z : ComplexSample (m := m) (n := n)) :
    complexSampleMatrix z*B+M = (complexSampleMatrix z+M*B⁻¹)*B := by
  rw [Matrix.add_mul,Matrix.mul_assoc,B.nonsing_inv_mul hB,Matrix.mul_one]

theorem correlatedColumnMinimum_bounds {m n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (M : Matrix (Fin m) (Fin n) ℂ) (hn : 0<n) (hB : IsUnit B.det)
    (z : ComplexSample (m := m) (n := n)) :
    correlatedColumnMinimum B M hn z ≤ matrixColumnControl B*
      complexNoncentralSampleSmallestEigenvalue (M*B⁻¹) hn z ∧
    complexNoncentralSampleSmallestEigenvalue (M*B⁻¹) hn z ≤
      matrixColumnControl B⁻¹*correlatedColumnMinimum B M hn z := by
  unfold correlatedColumnMinimum
  rw [correlatedColumn_sample_identity B M hB]
  exact ⟨gramSmallestValue_mul_column_upper _ B hn hB,
    gramSmallestValue_mul_column_lower _ B hn hB⟩

def actualCorrelatedColumnMinimumCDF (d n : ℕ) (B : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (M : Matrix (Fin (d+(n+1))) (Fin (n+1)) ℂ) (x : ℝ) : ℝ :=
  (stdGaussian (ComplexSample (m := d+(n+1)) (n := n+1))).real
    {z | correlatedColumnMinimum B M (Nat.succ_pos n) z≤x}

theorem actualCorrelatedColumnMinimumCDF_sandwich (d n : ℕ)
    (B : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hB : IsUnit B.det)
    (M : Matrix (Fin (d+(n+1))) (Fin (n+1)) ℂ) (x : ℝ) :
    actualNoncentralMinimumCDF d n (M*B⁻¹) (x/matrixColumnControl B) ≤
      actualCorrelatedColumnMinimumCDF d n B M x ∧
    actualCorrelatedColumnMinimumCDF d n B M x ≤
      actualNoncentralMinimumCDF d n (M*B⁻¹) (matrixColumnControl B⁻¹*x) := by
  constructor
  · apply measureReal_mono (h₂ := measure_ne_top _ _)
    intro z hz
    have hb := (correlatedColumnMinimum_bounds B M (Nat.succ_pos n) hB z).1
    have hz' : complexNoncentralSampleSmallestEigenvalue (M*B⁻¹) (Nat.succ_pos n) z ≤
        x/matrixColumnControl B := hz
    have hh := (le_div_iff₀ (matrixColumnControl_pos B)).mp hz'
    exact hb.trans (by nlinarith)
  · apply measureReal_mono (h₂ := measure_ne_top _ _)
    intro z hz
    exact (correlatedColumnMinimum_bounds B M (Nat.succ_pos n) hB z).2.trans
      (mul_le_mul_of_nonneg_left hz (matrixColumnControl_pos B⁻¹).le)

theorem actualCorrelatedColumnMinimumCDF_diversity (d n : ℕ)
    (B : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (hB : IsUnit B.det)
    (M : Matrix (Fin (d+(n+1))) (Fin (n+1)) ℂ) :
    Tendsto (fun x : ℝ => Real.log (actualCorrelatedColumnMinimumCDF d n B M x)/Real.log x)
      (𝓝[>] 0) (𝓝 ((d+1 : ℕ) : ℝ)) := by
  let c := noncentralMinimumPowerLower d n (M*B⁻¹)/(matrixColumnControl B)^(d+1)
  let C := noncentralMinimumPowerUpper d n (M*B⁻¹)*(matrixColumnControl B⁻¹)^(d+1)
  have hc : 0<c := div_pos (noncentralMinimumPower_constants_pos d n _).1
    (pow_pos (matrixColumnControl_pos B) _)
  have hC : 0<C := mul_pos (noncentralMinimumPower_constants_pos d n _).2
    (pow_pos (matrixColumnControl_pos B⁻¹) _)
  apply tendsto_log_ratio_of_power_bounds _ (d+1) c C hc hC
  have ha : (0 : ℝ)<matrixColumnControl B/4 := div_pos (matrixColumnControl_pos B) (by norm_num)
  have hBi : 0<matrixColumnControl B⁻¹ := matrixColumnControl_pos B⁻¹
  have hb : (0 : ℝ)<1/(4*matrixColumnControl B⁻¹) := by positivity
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds,
    (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with x hx hxa hxb
  have hxl : 0<x/matrixColumnControl B := div_pos hx (matrixColumnControl_pos B)
  have hxl1 : x/matrixColumnControl B≤1/4 := by
    rw [div_le_iff₀ (matrixColumnControl_pos B)]; linarith
  have hxu : 0<matrixColumnControl B⁻¹*x := mul_pos (matrixColumnControl_pos B⁻¹) hx
  have hxu1 : matrixColumnControl B⁻¹*x≤1/4 := by
    have hh := (lt_div_iff₀ (show 0<4*matrixColumnControl B⁻¹ by positivity)).mp hxb
    nlinarith
  have hl := (actualNoncentralMinimumCDF_local_power_bounds d n (M*B⁻¹) _ hxl hxl1).1
  have hu := (actualNoncentralMinimumCDF_local_power_bounds d n (M*B⁻¹) _ hxu hxu1).2
  have hs := actualCorrelatedColumnMinimumCDF_sandwich d n B hB M x
  refine ⟨hx,?_,?_⟩
  · calc
      c*x^(d+1) = noncentralMinimumPowerLower d n (M*B⁻¹)*(x/matrixColumnControl B)^(d+1) := by
        dsimp only [c]; rw [div_pow]; ring
      _ ≤ _ := hl.trans hs.1
  · calc
      _ ≤ noncentralMinimumPowerUpper d n (M*B⁻¹)*(matrixColumnControl B⁻¹*x)^(d+1) := hs.2.trans hu
      _ = C*x^(d+1) := by dsimp only [C]; rw [mul_pow]; ring

end
end JinWishart
#print axioms JinWishart.measurable_gramSmallestValue
#print axioms JinWishart.measurable_correlatedColumnMinimum
#print axioms JinWishart.correlatedColumn_sample_identity
#print axioms JinWishart.correlatedColumnMinimum_bounds
#print axioms JinWishart.actualCorrelatedColumnMinimumCDF_sandwich
#print axioms JinWishart.actualCorrelatedColumnMinimumCDF_diversity
