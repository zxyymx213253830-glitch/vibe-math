import JinWishartFormalization.GaussianComplexColumnFrame

/-!
# Fixed-column complex Gaussian inner product law

Use existing characteristic-function uniqueness and standard Gaussian formulas
to identify the actual off-diagonal projection law without selecting a QR basis.
[需人工审查] Real/complex characteristic-function and variance conventions.
-/

open MeasureTheory ProbabilityTheory

namespace JinWishart

noncomputable section

theorem complexColumn_real_inner {m : ℕ} (a z : ComplexColumnSpace m) :
    inner ℝ a z = (inner ℂ a z).re := by
  exact (real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two a z).trans
    (re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two
      (𝕜 := ℂ) a z).symm

theorem real_inner_complex_inner {m : ℕ} (a z : ComplexColumnSpace m) (t : ℂ) :
    inner ℝ (inner ℂ a z) t = inner ℝ z (t • a) := by
  rw [Complex.inner]
  rw [complexColumn_real_inner, inner_smul_right, inner_conj_symm]

theorem charFun_stdGaussian_complex_inner {m : ℕ} (a : ComplexColumnSpace m) (t : ℂ) :
    charFun ((stdGaussian (ComplexColumnSpace m)).map (fun z => inner ℂ a z)) t =
      Complex.exp (-‖t • a‖ ^ 2 / 2) := by
  calc
    _ = charFun (stdGaussian (ComplexColumnSpace m)) (t • a) := by
      rw [charFun_apply, integral_map (by fun_prop) (by fun_prop), charFun_apply]
      simp_rw [real_inner_complex_inner]
    _ = _ := charFun_stdGaussian _

/-- The full actual complex projection law, including the zero-vector case. -/
theorem stdGaussian_complex_inner_law {m : ℕ} (a : ComplexColumnSpace m) :
    (stdGaussian (ComplexColumnSpace m)).map (fun z => inner ℂ a z) =
      (stdGaussian ℂ).map (fun z => ‖a‖ • z) := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_stdGaussian_complex_inner, charFun_map_smul, charFun_stdGaussian]
  simp [norm_smul, mul_comm]

/-- Exact law in the paper's variance-one complex column convention. -/
theorem actualComplexColumn_inner_law {m : ℕ} (a : ComplexColumnSpace m) :
    (stdGaussian (TwoColumnBlock m)).map (fun v => inner ℂ a (actualComplexColumn v)) =
      (stdGaussian ℂ).map (fun z => ((Real.sqrt 2)⁻¹ * ‖a‖) • z) := by
  have hc := stdGaussian_map (complexColumnCoordinates m)
  calc
    _ = ((stdGaussian (TwoColumnBlock m)).map (complexColumnCoordinates m)).map
        (fun z => inner ℂ a ((Real.sqrt 2)⁻¹ • z)) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = (stdGaussian (ComplexColumnSpace m)).map
        (fun z => (Real.sqrt 2)⁻¹ • inner ℂ a z) := by
      rw [hc]
      congr 1
      funext z
      exact inner_smul_right_eq_smul _ _ _
    _ = ((stdGaussian (ComplexColumnSpace m)).map (fun z => inner ℂ a z)).map
        (fun z => (Real.sqrt 2)⁻¹ • z) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = ((stdGaussian ℂ).map (fun z => ‖a‖ • z)).map
        (fun z => (Real.sqrt 2)⁻¹ • z) := by
      rw [stdGaussian_complex_inner_law]
    _ = _ := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
      funext z
      exact smul_smul _ _ _

/-- The actual Gram off-diagonal law with the first column fixed, for any row count. -/
theorem twoColumnGram_offDiagonal_fixed_first_law {m : ℕ} (u : TwoColumnBlock m) :
    (stdGaussian (TwoColumnBlock m)).map
      (fun v => complexGram (complexSampleMatrix (twoColumnJoin (u, v))) 0 1) =
      (stdGaussian ℂ).map (fun z => ((Real.sqrt 2)⁻¹ * ‖actualComplexColumn u‖) • z) := by
  simpa [twoColumnJoin_matrix_eq_columnPair, complexColumnPair_gram_entry] using
    actualComplexColumn_inner_law (actualComplexColumn u)

end

end JinWishart
