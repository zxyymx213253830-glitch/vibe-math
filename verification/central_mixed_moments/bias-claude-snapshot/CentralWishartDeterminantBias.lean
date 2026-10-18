import JinWishartFormalization.CentralWishartPrincipalMinorMoments
import JinWishartFormalization.CentralWishartMatrixDensity

/-!
# Actual determinant-power bias of complex Wishart laws

Codex proof bodies. Qoder route consultation, not an assumed target density.
[需人工审查] Weighted measures, actual Gaussian parameter/variance convention.
-/
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal ComplexOrder
namespace JinWishart
noncomputable section

def centralDeterminantPowerMoment (d n p : ℕ) : ℝ :=
  ∏ j : Fin n, ((Nat.factorial (d+j.val+p) : ℕ) : ℝ) /
    ((Nat.factorial (d+j.val) : ℕ) : ℝ)

theorem centralDeterminantPowerMoment_pos (d n p : ℕ) :
    0 < centralDeterminantPowerMoment d n p := by
  apply Finset.prod_pos
  intro j _
  positivity

theorem centralWishartDensityConstant_power_bias (d n p : ℕ) :
    centralWishartDensityConstant d n =
      centralDeterminantPowerMoment d n p * centralWishartDensityConstant (d+p) n := by
  unfold centralWishartDensityConstant centralDeterminantPowerMoment
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [show d+p+j.val = d+j.val+p by omega]
  have h0 : ((Nat.factorial (d+j.val) : ℕ) : ℝ) ≠ 0 := by positivity
  have h1 : ((Nat.factorial (d+j.val+p) : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

theorem centralWishartMatrixDensity_power_bias (d n p : ℕ)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    centralWishartMatrixDensity d n A * ENNReal.ofReal (‖A.det‖^p) =
      ENNReal.ofReal (centralDeterminantPowerMoment d n p) *
        centralWishartMatrixDensity (d+p) n A := by
  classical
  unfold centralWishartMatrixDensity
  by_cases hA : A.PosDef
  · rw [if_pos hA, if_pos hA]
    have hd : 0 ≤ A.det.re := (Complex.nonneg_iff.mp hA.det_pos.le).1
    have hK := (centralWishartDensityConstant_pos d n).le
    have hD : 0 ≤ centralWishartDensityConstant d n * A.det.re ^ d * Real.exp (-A.trace.re) := by positivity
    rw [complex_norm_eq_re_of_nonneg _ hA.det_pos.le,
      ← ENNReal.ofReal_mul hD,
      ← ENNReal.ofReal_mul (centralDeterminantPowerMoment_pos d n p).le]
    congr 1
    rw [centralWishartDensityConstant_power_bias d n p, pow_add]
    ring
  · rw [if_neg hA, if_neg hA]
    simp

/-- Weighting the ACTUAL law by det(W)^p adds p rows, with explicit mass. -/
theorem complexWishart_determinant_power_bias (d n p : ℕ) :
    (complexWishart (m := d+n) (n := n)).withDensity
      (fun A => ENNReal.ofReal (‖A.det‖^p)) =
      ENNReal.ofReal (centralDeterminantPowerMoment d n p) •
        complexWishart (m := (d+p)+n) (n := n) := by
  have hD := measurable_centralWishartMatrixDensity d n
  have hP : Measurable (fun A : Matrix (Fin n) (Fin n) ℂ =>
      ENNReal.ofReal (‖A.det‖^p)) := by fun_prop
  rw [complexWishart_eq_matrixDensity, complexWishart_eq_matrixDensity,
    ← withDensity_mul _ hD hP, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  apply withDensity_congr_ae
  exact ae_of_all _ (centralWishartMatrixDensity_power_bias d n p)

theorem lintegral_complexWishart_determinant_power_bias (d n p : ℕ)
    (f : Matrix (Fin n) (Fin n) ℂ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ A, ENNReal.ofReal (‖A.det‖^p) * f A ∂complexWishart (m := d+n) (n := n)) =
      ENNReal.ofReal (centralDeterminantPowerMoment d n p) *
        ∫⁻ A, f A ∂complexWishart (m := (d+p)+n) (n := n) := by
  have h := congrArg (fun μ => ∫⁻ A, f A ∂μ)
    (complexWishart_determinant_power_bias d n p)
  rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hf,
    lintegral_smul_measure] at h
  simpa only [Pi.mul_apply, smul_eq_mul] using h

theorem complexWishart_principalSubmatrix_norm_moment (t n k q : ℕ)
    (e : Fin k → Fin n) (he : Function.Injective e) (ht : k ≤ t) :
    (∫⁻ A, ENNReal.ofReal (‖(A.submatrix e e).det‖^q)
      ∂complexWishart (m := t) (n := n)) =
        ENNReal.ofReal (centralDeterminantPowerMoment (t-k) k q) := by
  have h := complexWishart_determinant_norm_moment (t-k) k q
  rw [show t-k+k=t by omega] at h
  rw [← complexWishart_principalSubmatrix_law (m := t) e he,
    lintegral_map (by fun_prop) (by fun_prop)] at h
  rw [h]
  exact (ENNReal.ofReal_prod_of_nonneg (fun _ _ => by positivity)).symm

/-- A full principal block and a nested selected minor share a precise moment.
This does not assert independence or arbitrary partially overlapping blocks. -/
theorem complexWishart_nested_determinant_moment (d n k p q : ℕ)
    (e : Fin k → Fin n) (he : Function.Injective e) :
    (∫⁻ A, ENNReal.ofReal (‖A.det‖^p) * ENNReal.ofReal (‖(A.submatrix e e).det‖^q)
      ∂complexWishart (m := d+n) (n := n)) =
      ENNReal.ofReal (centralDeterminantPowerMoment d n p) *
        ENNReal.ofReal (centralDeterminantPowerMoment ((d+p)+n-k) k q) := by
  have hk : k ≤ n := by simpa using Fintype.card_le_of_injective e he
  rw [lintegral_complexWishart_determinant_power_bias d n p _ (by fun_prop),
    complexWishart_principalSubmatrix_norm_moment ((d+p)+n) n k q e he (by omega)]

end
end JinWishart
#print axioms JinWishart.centralDeterminantPowerMoment_pos
#print axioms JinWishart.centralWishartDensityConstant_power_bias
#print axioms JinWishart.centralWishartMatrixDensity_power_bias
#print axioms JinWishart.complexWishart_determinant_power_bias
#print axioms JinWishart.lintegral_complexWishart_determinant_power_bias
#print axioms JinWishart.complexWishart_principalSubmatrix_norm_moment
#print axioms JinWishart.complexWishart_nested_determinant_moment
