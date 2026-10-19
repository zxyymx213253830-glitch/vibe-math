import JinWishartFormalization.CentralMinimumDiversity
import JinWishartFormalization.WishartGamma

/-!
# Central minimum diversity: every nonempty rectangular shape

The scalar branch uses its actual Gamma pushforward law, not a dummy residual.
Codex. [需人工审查] Actual event/shape/logarithmic interpretation.
-/
open Filter MeasureTheory ProbabilityTheory Matrix
open scoped Topology
namespace JinWishart
noncomputable section

theorem actualCentralMinimumCDF_oneColumn (d : ℕ) (x : ℝ) :
    actualCentralMinimumCDF d 0 x = cdf (gammaMeasure ((d+1 : ℕ) : ℝ) 1) x := by
  letI : IsProbabilityMeasure (gammaMeasure ((d+1 : ℕ) : ℝ) 1) :=
    isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
  rw [cdf_eq_real,← centralColumnSmallestEigenvalue_map_eq_gammaMeasure (Nat.succ_pos d)]
  change ((stdGaussian (ComplexSample (m := d+1) (n := 1)))
    {z | centralGaussianSampleMinimum (d+1) 1 (by omega) z ≤ x}).toReal =
    (((stdGaussian (ComplexSample (m := d+1) (n := 1))).map
      (complexNoncentralSampleSmallestEigenvalue (0 : Matrix (Fin (d+1)) (Fin 1) ℂ)
        (by omega))) (Set.Iic x)).toReal
  rw [Measure.map_apply (measurable_complexNoncentralSampleSmallestEigenvalue _ _) measurableSet_Iic]
  rfl

theorem actualCentralMinimumCDF_all_local_power_bounds (d n : ℕ)
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    (Real.exp (-1)/(Nat.factorial (d+1) : ℝ))*x^(d+1) ≤ actualCentralMinimumCDF d n x ∧
    actualCentralMinimumCDF d n x ≤
      (((n+1 : ℕ) : ℝ)^(d+2)/(Nat.factorial (d+1) : ℝ))*x^(d+1) := by
  cases n with
  | succ n => exact actualCentralMinimumCDF_local_power_bounds d (n+1) (Nat.succ_pos n) x hx hx1
  | zero =>
    rw [actualCentralMinimumCDF_oneColumn]
    constructor
    · apply le_trans _ (cdf_gammaMeasure_nat_power_lower d x hx.le)
      have he := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hx1))
        (show 0 ≤ x^(d+1)/(Nat.factorial (d+1) : ℝ) from by positivity)
      simpa only [div_mul_eq_mul_div,mul_div_assoc] using he
    · simpa only [zero_add,Nat.cast_one,one_pow,one_div,inv_mul_eq_div] using
        cdf_gammaMeasure_nat_power_upper d x hx.le

theorem actualCentralMinimumCDF_all_diversity (d n : ℕ) :
    Tendsto (fun x : ℝ => Real.log (actualCentralMinimumCDF d n x) / Real.log x)
      (𝓝[>] 0) (𝓝 ((d+1 : ℕ) : ℝ)) := by
  apply tendsto_log_ratio_of_power_bounds _ (d+1)
    (Real.exp (-1)/(Nat.factorial (d+1) : ℝ))
    (((n+1 : ℕ) : ℝ)^(d+2)/(Nat.factorial (d+1) : ℝ))
  · positivity
  · positivity
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ)<1)).filter_mono nhdsWithin_le_nhds] with x hx hx1
    exact ⟨hx,actualCentralMinimumCDF_all_local_power_bounds d n x hx hx1.le⟩

theorem actualCentralRectangular_minimum_diversity (m n : ℕ) (hn : 0 < n) (hnm : n ≤ m) :
    Tendsto (fun x : ℝ => Real.log
      ((stdGaussian (ComplexSample (m := m) (n := n))).real
        {z | centralGaussianSampleMinimum m n hn z ≤ x}) / Real.log x)
      (𝓝[>] 0) (𝓝 ((m-n+1 : ℕ) : ℝ)) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hm : m-(k+1)+(k+1)=m := Nat.sub_add_cancel hnm
  generalize hd : m-(k+1)=d at *
  subst m
  exact actualCentralMinimumCDF_all_diversity d k

end
end JinWishart
#print axioms JinWishart.actualCentralMinimumCDF_oneColumn
#print axioms JinWishart.actualCentralMinimumCDF_all_local_power_bounds
#print axioms JinWishart.actualCentralMinimumCDF_all_diversity
#print axioms JinWishart.actualCentralRectangular_minimum_diversity
