import JinWishartFormalization.OrderedSquareGapMoments
import JinWishartFormalization.Theorem1CentralTwoRowActualCDF
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Codex. Seed2026102409 exact lower-Gamma/moment controls before source.
Truncated exponential moments and the ORIGINAL central2x2 T2 matrix determinant.
[需人工审查] Compact integrability, density conversion, and interval endpoints. -/
open MeasureTheory Set
open scoped ENNReal
namespace JinWishart
noncomputable section

def exponentialIntervalMeasure (x : ℝ) : Measure ℝ :=
  (volume.restrict (Ioc 0 x)).withDensity (fun y => ENNReal.ofReal (Real.exp (-y)))

theorem exponentialIntervalMeasure_isFinite (x : ℝ) : IsFiniteMeasure (exponentialIntervalMeasure x) := by
  have hi : IntegrableOn (fun y : ℝ => Real.exp (-y)) (Ioc 0 x) :=
    (by fun_prop : Continuous (fun y : ℝ => Real.exp (-y))).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  apply isFiniteMeasure_withDensity
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun y => Real.exp_nonneg (-y))]
  exact ENNReal.ofReal_ne_top

attribute [instance] exponentialIntervalMeasure_isFinite

theorem exponentialInterval_integrable_pow (x : ℝ) (k : ℕ) :
    Integrable (fun y : ℝ => y^k) (exponentialIntervalMeasure x) := by
  unfold exponentialIntervalMeasure
  rw [integrable_withDensity_iff_integrable_smul' (by fun_prop) (ae_of_all _ fun y => by finiteness)]
  have hi : IntegrableOn (fun y : ℝ => Real.exp (-y)*y^k) (Ioc 0 x) :=
    (by fun_prop : Continuous (fun y : ℝ => Real.exp (-y)*y^k)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  simpa [IntegrableOn,ENNReal.toReal_ofReal,Real.exp_nonneg,smul_eq_mul] using hi

theorem partialGamma_nat_succ_eq_realInterval (k : ℕ) (x : ℝ) :
    Complex.partialGamma ((k+1 : ℕ) : ℂ) x=
      ((∫ y in (0 : ℝ)..x,y^k*Real.exp (-y) : ℝ) : ℂ) := by
  rw [Complex.partialGamma]
  have hfun : (fun y : ℝ => (-y).exp*(y : ℂ)^(((k+1 : ℕ) : ℂ)-1))=
      (fun y : ℝ => ((y^k*Real.exp (-y) : ℝ) : ℂ)) := by
    funext y
    rw [show ((k+1 : ℕ) : ℂ)-1=(k : ℂ) by push_cast;ring,Complex.cpow_natCast]
    push_cast
    ring
  rw [hfun,intervalIntegral.integral_ofReal]

theorem exponentialInterval_integral_pow_eq_partialGamma (x : ℝ) (hx : 0≤x) (k : ℕ) :
    ((∫ y : ℝ,y^k ∂exponentialIntervalMeasure x : ℝ) : ℂ)=
      Complex.partialGamma ((k+1 : ℕ) : ℂ) x := by
  rw [partialGamma_nat_succ_eq_realInterval]
  congr 1
  unfold exponentialIntervalMeasure
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (ae_of_all _ fun y => by finiteness)]
  simp only [ENNReal.toReal_ofReal (Real.exp_nonneg _),smul_eq_mul]
  rw [intervalIntegral.integral_of_le hx]
  apply integral_congr_ae
  exact ae_of_all _ fun y => mul_comm _ _

theorem theorem2CentralTwoRow_XiDet_eq_intervalMoments (x : ℝ) (hx : 0≤x) :
    (theorem2XiMatrix 2 2 0 (by omega) (by omega) (fun j : Fin 0 => Fin.elim0 j) x).det=
      (twoMomentDeterminant (exponentialIntervalMeasure x) : ℂ) := by
  have hm : theorem2XiMatrix 2 2 0 (by omega) (by omega) (fun j : Fin 0 => Fin.elim0 j) x=
      (!![((∫ y : ℝ,y^2 ∂exponentialIntervalMeasure x : ℝ) : ℂ),
          ((∫ y : ℝ,y ∂exponentialIntervalMeasure x : ℝ) : ℂ);
          ((∫ y : ℝ,y ∂exponentialIntervalMeasure x : ℝ) : ℂ),
          ((∫ _ : ℝ,(1 : ℝ) ∂exponentialIntervalMeasure x : ℝ) : ℂ)] : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [theorem2XiMatrix,theorem2XiEntry,theorem1GammaIndex]
    · simpa using (exponentialInterval_integral_pow_eq_partialGamma x hx 2).symm
    · simpa using (exponentialInterval_integral_pow_eq_partialGamma x hx 1).symm
    · simpa using (exponentialInterval_integral_pow_eq_partialGamma x hx 1).symm
    · simpa using (exponentialInterval_integral_pow_eq_partialGamma x hx 0).symm
  rw [hm,Matrix.det_fin_two]
  change ((∫ y : ℝ,y^2 ∂exponentialIntervalMeasure x : ℝ) : ℂ)*
      ((∫ _ : ℝ,(1 : ℝ) ∂exponentialIntervalMeasure x : ℝ) : ℂ)-
      ((∫ y : ℝ,y ∂exponentialIntervalMeasure x : ℝ) : ℂ)*
      ((∫ y : ℝ,y ∂exponentialIntervalMeasure x : ℝ) : ℂ)=_
  unfold twoMomentDeterminant
  push_cast
  ring

end
end JinWishart
#print axioms JinWishart.exponentialIntervalMeasure_isFinite
#print axioms JinWishart.exponentialInterval_integrable_pow
#print axioms JinWishart.partialGamma_nat_succ_eq_realInterval
#print axioms JinWishart.exponentialInterval_integral_pow_eq_partialGamma
#print axioms JinWishart.theorem2CentralTwoRow_XiDet_eq_intervalMoments
