import JinWishartFormalization.GaussianShiftMeasureComparison
import JinWishartFormalization.CentralMinimumScaledDiversity

/-!
# Actual arbitrary-mean minimum CDF compared to two central covariance laws

Codex. Constants may depend on the FIXED mean; not a uniform growing-mean result.
[需人工审查] Shifted Gaussian event transport and complex variance convention.
-/
open Matrix MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

def gaussianShiftLowerConstant {ι : Type*} [Fintype ι] (y : EuclideanSpace ℝ ι) : ℝ :=
  ((2 : ℝ)^Fintype.card ι)⁻¹*Real.exp (-‖y‖^2)

def gaussianShiftUpperConstant {ι : Type*} [Fintype ι] (y : EuclideanSpace ℝ ι) : ℝ :=
  (2 : ℝ)^Fintype.card ι*Real.exp (‖y‖^2)

theorem stdGaussian_shift_real_event_bounds {ι : Type*} [Fintype ι]
    (y : EuclideanSpace ℝ ι) (S : Set (EuclideanSpace ℝ ι)) (hS : MeasurableSet S) :
    gaussianShiftLowerConstant y * (stdGaussian (EuclideanSpace ℝ ι)).real
      ((fun z => (1/2 : ℝ) • z) ⁻¹' S) ≤
        (stdGaussian (EuclideanSpace ℝ ι)).real ((fun z => z+y) ⁻¹' S) ∧
    (stdGaussian (EuclideanSpace ℝ ι)).real ((fun z => z+y) ⁻¹' S) ≤
      gaussianShiftUpperConstant y * (stdGaussian (EuclideanSpace ℝ ι)).real
        ((fun z => (2 : ℝ) • z) ⁻¹' S) := by
  have hl := Measure.le_iff.mp (stdGaussian_shift_measure_lower y) S hS
  have hu := Measure.le_iff.mp (stdGaussian_shift_measure_upper y) S hS
  have hlR := ENNReal.toReal_mono (by finiteness) hl
  have huR := ENNReal.toReal_mono (by
    rw [Measure.smul_apply,smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hu
  rw [Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity),Measure.map_apply (by fun_prop) hS,
    Measure.map_apply (by fun_prop) hS] at hlR
  rw [Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity),Measure.map_apply (by fun_prop) hS,
    Measure.map_apply (by fun_prop) hS] at huR
  exact ⟨hlR,huR⟩

def actualNoncentralMinimumCDF (d n : ℕ)
    (M : Matrix (Fin (d+(n+1))) (Fin (n+1)) ℂ) (x : ℝ) : ℝ :=
  (stdGaussian (ComplexSample (m := d+(n+1)) (n := n+1))).real
    {z | complexNoncentralSampleSmallestEigenvalue M (Nat.succ_pos n) z ≤ x}

theorem centralGaussianSampleMinimum_shift {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (hn : 0 < n) (z : ComplexSample (m := m) (n := n)) :
    centralGaussianSampleMinimum m n hn (z+complexSampleMean M) =
      complexNoncentralSampleSmallestEigenvalue M hn z := by
  simp only [centralGaussianSampleMinimum,complexNoncentralSampleSmallestEigenvalue,
    complexSampleMatrix_add_mean,zero_add,add_zero]

theorem actualNoncentralMinimumCDF_central_comparison (d n : ℕ)
    (M : Matrix (Fin (d+(n+1))) (Fin (n+1)) ℂ) (x : ℝ) :
    gaussianShiftLowerConstant (complexSampleMean M) *
      actualCentralCovarianceMinimumCDF d n (1/4) x ≤ actualNoncentralMinimumCDF d n M x ∧
    actualNoncentralMinimumCDF d n M x ≤
      gaussianShiftUpperConstant (complexSampleMean M)*actualCentralCovarianceMinimumCDF d n 4 x := by
  have h := stdGaussian_shift_real_event_bounds (complexSampleMean M)
    {z | centralGaussianSampleMinimum (d+(n+1)) (n+1) (Nat.succ_pos n) z ≤ x}
    (measurableSet_le (measurable_centralGaussianSampleMinimum _ _ _) measurable_const)
  have hhalf : Real.sqrt (1/4 : ℝ)=1/2 := by norm_num [Real.sqrt_div]
  have htwo : Real.sqrt (4 : ℝ)=2 := by norm_num
  simpa only [Set.preimage_setOf_eq,centralGaussianSampleMinimum_shift,
    actualCentralCovarianceMinimumCDF,actualNoncentralMinimumCDF,hhalf,htwo] using h

end
end JinWishart
#print axioms JinWishart.stdGaussian_shift_real_event_bounds
#print axioms JinWishart.centralGaussianSampleMinimum_shift
#print axioms JinWishart.actualNoncentralMinimumCDF_central_comparison
