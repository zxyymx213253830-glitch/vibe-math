import JinWishartFormalization.CentralWishartClosedDensity

/-!
# Integer power bias and moments of positive-integer Gamma laws

Codex proof bodies. Shape shift reuses actual normalized Gamma densities and
strictly positive support; it does not introduce a radial integral assumption.
[需人工审查] Weighted-measure and nonnegative moment interpretation.
-/
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace JinWishart
noncomputable section

theorem gammaPDF_nat_power_shift (k p : ℕ) (r : ℝ) (hr : 0 < r) :
    gammaPDF ((k + 1 : ℕ) : ℝ) 1 r * ENNReal.ofReal (r ^ p) =
      ENNReal.ofReal (((Nat.factorial (k + p) : ℕ) : ℝ) /
        ((Nat.factorial k : ℕ) : ℝ)) * gammaPDF ((k + p + 1 : ℕ) : ℝ) 1 r := by
  rw [gammaPDF_nat_succ_positive k r hr, gammaPDF_nat_succ_positive (k + p) r hr,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [pow_add]
  have hk : ((Nat.factorial k : ℕ) : ℝ) ≠ 0 := by positivity
  have hkp : ((Nat.factorial (k + p) : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp

theorem gammaMeasure_nat_power_bias (k p : ℕ) :
    (gammaMeasure ((k + 1 : ℕ) : ℝ) 1).withDensity (fun r => ENNReal.ofReal (r ^ p)) =
      ENNReal.ofReal (((Nat.factorial (k + p) : ℕ) : ℝ) /
        ((Nat.factorial k : ℕ) : ℝ)) • gammaMeasure ((k + p + 1 : ℕ) : ℝ) 1 := by
  have hG : Measurable (gammaPDF ((k + 1 : ℕ) : ℝ) 1) :=
    ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal _ _)
  have hP : Measurable (fun r : ℝ => ENNReal.ofReal (r ^ p)) := by fun_prop
  rw [gammaMeasure_nat_succ_eq_positive_density k,
    gammaMeasure_nat_succ_eq_positive_density (k + p),
    ← withDensity_mul _ hG hP, ← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  exact gammaPDF_nat_power_shift k p r hr

theorem lintegral_gammaMeasure_nat_power (k p : ℕ) :
    ∫⁻ r, ENNReal.ofReal (r ^ p) ∂gammaMeasure ((k + 1 : ℕ) : ℝ) 1 =
      ENNReal.ofReal (((Nat.factorial (k + p) : ℕ) : ℝ) /
        ((Nat.factorial k : ℕ) : ℝ)) := by
  letI : IsProbabilityMeasure (gammaMeasure ((k + p + 1 : ℕ) : ℝ) 1) :=
    isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
  have h := congrArg (fun μ : Measure ℝ => μ Set.univ) (gammaMeasure_nat_power_bias k p)
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    Measure.smul_apply, measure_univ] at h
  simpa only [smul_eq_mul, mul_one] using h

theorem lintegral_gammaMeasure_nat_abs_power (k p : ℕ) :
    ∫⁻ r, ENNReal.ofReal (|r| ^ p) ∂gammaMeasure ((k + 1 : ℕ) : ℝ) 1 =
      ENNReal.ofReal (((Nat.factorial (k + p) : ℕ) : ℝ) /
        ((Nat.factorial k : ℕ) : ℝ)) := by
  rw [← lintegral_gammaMeasure_nat_power k p]
  apply lintegral_congr_ae
  have hp : ∀ᵐ r ∂gammaMeasure ((k + 1 : ℕ) : ℝ) 1, 0 < r :=
    (gammaMeasure_nat_succ_absolutelyContinuous_positive k).ae_le
      (ae_restrict_mem measurableSet_Ioi)
  filter_upwards [hp] with r hr
  rw [abs_of_pos hr]

end
end JinWishart

#print axioms JinWishart.gammaPDF_nat_power_shift
#print axioms JinWishart.gammaMeasure_nat_power_bias
#print axioms JinWishart.lintegral_gammaMeasure_nat_power
#print axioms JinWishart.lintegral_gammaMeasure_nat_abs_power
