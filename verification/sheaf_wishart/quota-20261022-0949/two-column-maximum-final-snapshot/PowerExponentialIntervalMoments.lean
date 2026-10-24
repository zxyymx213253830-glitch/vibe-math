import JinWishartFormalization.ExponentialIntervalMoments

/-! Codex. Seed2026102415 before source. Truncated integer Gamma moments.
[需人工审查] Compact integrability and signed interval versus restricted measure. -/
open MeasureTheory Set Matrix
open scoped ENNReal
namespace JinWishart
noncomputable section

def powerExponentialIntervalMeasure (d : ℕ) (x : ℝ) : Measure ℝ :=
  (volume.restrict (Ioc 0 x)).withDensity
    (fun y => ENNReal.ofReal (|y|^d*Real.exp (-y)))

theorem powerExponentialIntervalMeasure_isFinite (d : ℕ) (x : ℝ) :
    IsFiniteMeasure (powerExponentialIntervalMeasure d x) := by
  have hi : IntegrableOn (fun y : ℝ => |y|^d*Real.exp (-y)) (Ioc 0 x) :=
    (by fun_prop : Continuous (fun y : ℝ => |y|^d*Real.exp (-y))).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  apply isFiniteMeasure_withDensity
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun y => by positivity)]
  exact ENNReal.ofReal_ne_top
attribute [instance] powerExponentialIntervalMeasure_isFinite

theorem powerExponentialInterval_integrable_pow (d : ℕ) (x : ℝ) (k : ℕ) :
    Integrable (fun y : ℝ => y^k) (powerExponentialIntervalMeasure d x) := by
  unfold powerExponentialIntervalMeasure
  rw [integrable_withDensity_iff_integrable_smul' (by fun_prop) (ae_of_all _ fun y => by finiteness)]
  have hi : IntegrableOn (fun y : ℝ => (|y|^d*Real.exp (-y))*y^k) (Ioc 0 x) :=
    (by fun_prop : Continuous (fun y : ℝ => (|y|^d*Real.exp (-y))*y^k)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hN (y : ℝ) : 0≤|y|^d*Real.exp (-y) := by positivity
  simpa only [IntegrableOn,ENNReal.toReal_ofReal (hN _),smul_eq_mul] using hi

theorem powerExponentialInterval_integral_pow_eq_partialGamma (d : ℕ) (x : ℝ) (hx : 0≤x) (k : ℕ) :
    ((∫ y : ℝ,y^k ∂powerExponentialIntervalMeasure d x : ℝ) : ℂ)=
      Complex.partialGamma ((d+k+1 : ℕ) : ℂ) x := by
  rw [partialGamma_nat_succ_eq_realInterval]
  congr 1
  unfold powerExponentialIntervalMeasure
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop) (ae_of_all _ fun y => by finiteness)]
  simp only [smul_eq_mul]
  rw [intervalIntegral.integral_of_le hx]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
  rw [ENNReal.toReal_ofReal (by positivity : 0≤|y|^d*Real.exp (-y)),abs_of_pos hy.1,pow_add]
  ring

theorem theorem2CentralTwoColumn_XiDet_eq_intervalMoments (d : ℕ) (x : ℝ) (hx : 0≤x) :
    (theorem2XiMatrix 2 (d+2) 0 (by omega) (by omega) (fun j : Fin 0 => Fin.elim0 j) x).det=
      (twoMomentDeterminant (powerExponentialIntervalMeasure d x) : ℂ) := by
  have hm : theorem2XiMatrix 2 (d+2) 0 (by omega) (by omega) (fun j : Fin 0 => Fin.elim0 j) x=
      (!![((∫ y : ℝ,y^2 ∂powerExponentialIntervalMeasure d x : ℝ) : ℂ),
          ((∫ y : ℝ,y ∂powerExponentialIntervalMeasure d x : ℝ) : ℂ);
          ((∫ y : ℝ,y ∂powerExponentialIntervalMeasure d x : ℝ) : ℂ),
          ((∫ _ : ℝ,(1 : ℝ) ∂powerExponentialIntervalMeasure d x : ℝ) : ℂ)] : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [theorem2XiMatrix,theorem2XiEntry,theorem1GammaIndex]
    · convert (powerExponentialInterval_integral_pow_eq_partialGamma d x hx 2).symm using 1 <;> norm_num <;> congr 1 <;> ring
    · convert (powerExponentialInterval_integral_pow_eq_partialGamma d x hx 1).symm using 1 <;> norm_num <;> congr 1 <;> ring
    · convert (powerExponentialInterval_integral_pow_eq_partialGamma d x hx 1).symm using 1 <;> norm_num <;> congr 1 <;> ring
    · simpa using (powerExponentialInterval_integral_pow_eq_partialGamma d x hx 0).symm
  rw [hm,Matrix.det_fin_two]
  change ((∫ y : ℝ,y^2 ∂powerExponentialIntervalMeasure d x : ℝ) : ℂ)*
    ((∫ _ : ℝ,(1 : ℝ) ∂powerExponentialIntervalMeasure d x : ℝ) : ℂ)-
    ((∫ y : ℝ,y ∂powerExponentialIntervalMeasure d x : ℝ) : ℂ)*
    ((∫ y : ℝ,y ∂powerExponentialIntervalMeasure d x : ℝ) : ℂ)=_
  unfold twoMomentDeterminant
  push_cast
  ring
end
end JinWishart
#print axioms JinWishart.powerExponentialIntervalMeasure_isFinite
#print axioms JinWishart.powerExponentialInterval_integrable_pow
#print axioms JinWishart.powerExponentialInterval_integral_pow_eq_partialGamma
#print axioms JinWishart.theorem2CentralTwoColumn_XiDet_eq_intervalMoments
