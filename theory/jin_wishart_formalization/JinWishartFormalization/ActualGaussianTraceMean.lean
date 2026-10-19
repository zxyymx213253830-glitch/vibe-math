import JinWishartFormalization.GaussianSquaredNormShift
import JinWishartFormalization.GammaIntegerMoments
import JinWishartFormalization.LogDetLowScale

/-! Exact expected power for the actual variance-one complex Gaussian matrix.
Codex proof bodies. Reuses the existing Gamma energy law and centered shift.
[需人工审查] Gaussian normalization, Bochner transport and model correspondence.
-/
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
namespace JinWishart
noncomputable section

theorem integral_complexSample_half_norm_sq (m n : ℕ) :
    (∫ z : ComplexSample (m := m) (n := n), ‖z‖^2/2 ∂stdGaussian _) = ((m*n : ℕ) : ℝ) := by
  by_cases hmn : m*n = 0
  · rcases Nat.mul_eq_zero.mp hmn with hm | hn
    · subst m
      have hz (z : ComplexSample (m := 0) (n := n)) : z = 0 := Subsingleton.elim _ _
      simp only [hz,norm_zero,zero_pow (by decide : 2 ≠ 0),zero_div,integral_zero]
      simp
    · subst n
      have hz (z : ComplexSample (m := m) (n := 0)) : z = 0 := Subsingleton.elim _ _
      simp only [hz,norm_zero,zero_pow (by decide : 2 ≠ 0),zero_div,integral_zero]
      simp
  · have hp : 0 < m*n := Nat.pos_of_ne_zero hmn
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hmn
    have hLaw := stdGaussian_half_norm_sq_law (E := ComplexSample (m := m) (n := n))
      (m*n) hp (by
        simp [ComplexSample,Module.finrank_fintype_fun_eq_card,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm])
    have h := congrArg (fun μ : Measure ℝ => ∫⁻ r, ENNReal.ofReal r ∂μ) hLaw
    rw [lintegral_map (by fun_prop) (by fun_prop)] at h
    have hG := lintegral_gammaMeasure_nat_power k 1
    simp only [pow_one] at hG
    have hc : ((Nat.factorial (k+1) : ℕ) : ℝ)/((Nat.factorial k : ℕ) : ℝ) = (k+1 : ℕ) := by
      rw [Nat.factorial_succ,Nat.cast_mul]
      exact mul_div_cancel_right₀ _ (by positivity)
    rw [hc] at hG
    rw [hk] at h
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun z => by positivity)) (by fun_prop)]
    rw [show (∫⁻ z : ComplexSample (m := m) (n := n), ENNReal.ofReal (‖z‖^2/2) ∂stdGaussian _) =
      ENNReal.ofReal ((k+1 : ℕ) : ℝ) from h.trans hG]
    rw [ENNReal.toReal_ofReal (by positivity),hk]

theorem complexSampleMean_half_norm_sq {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) :
    ‖complexSampleMean M‖^2/2 = ∑ i, ∑ j, ‖M i j‖^2 := by
  have h := complexSampleGram_trace_half_norm (complexSampleMean M)
  rw [complexSampleGram,complexSampleMatrix_complexSampleMean,complexGram_trace_re] at h
  exact h.symm

theorem actualExpectedGramPower_eq_closed {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) :
    actualExpectedGramPower M = (m*n : ℕ)+∑ i, ∑ j, ‖M i j‖^2 := by
  have he (z : ComplexSample (m := m) (n := n)) :
      (complexGram (complexSampleMatrix z+M)).trace.re = ‖z+complexSampleMean M‖^2/2 := by
    have h := complexSampleGram_trace_half_norm (z+complexSampleMean M)
    simpa only [complexSampleGram,complexSampleMatrix_add_mean] using h
  unfold actualExpectedGramPower
  simp_rw [he]
  rw [integral_div,integral_stdGaussian_norm_sq_add,add_div,
    ← integral_div,integral_complexSample_half_norm_sq,complexSampleMean_half_norm_sq]

theorem actualNoncentralMatrixLogDet_closed_mean_bound {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (M : Matrix (Fin m) (Fin n) ℂ) (r : ℝ) (hr : 0 ≤ r) :
    (∫ z, actualNoncentralMatrixLogDet M r z ∂stdGaussian _) ≤
      (min m n : ℕ)*Real.log (1+r*((m*n : ℕ)+∑ i, ∑ j, ‖M i j‖^2)/(min m n : ℕ)) := by
  simpa only [actualExpectedGramPower_eq_closed] using
    actualNoncentralMatrixLogDet_min_dimension_mean_bound hm hn M r hr

theorem actualNoncentralMatrixLogDet_closed_low_scale {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) :
    Tendsto (fun r : ℝ => (∫ z, actualNoncentralMatrixLogDet M r z ∂stdGaussian _)/r)
      (𝓝[>] 0) (𝓝 ((m*n : ℕ)+∑ i, ∑ j, ‖M i j‖^2)) := by
  simpa only [actualExpectedGramPower_eq_closed] using actualNoncentralMatrixLogDet_low_scale M

end
end JinWishart
#print axioms JinWishart.integral_complexSample_half_norm_sq
#print axioms JinWishart.complexSampleMean_half_norm_sq
#print axioms JinWishart.actualExpectedGramPower_eq_closed
#print axioms JinWishart.actualNoncentralMatrixLogDet_closed_mean_bound
#print axioms JinWishart.actualNoncentralMatrixLogDet_closed_low_scale
