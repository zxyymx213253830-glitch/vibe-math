import JinWishartFormalization.CentralWishartPrincipalMinorMoments
import JinWishartFormalization.HermitianShiftDeterminant
import JinWishartFormalization.CentralWishartMatrixDensity
import JinWishartFormalization.CentralWishartMinimum

/-!
# Finite shifted determinant mean and the actual cone-integral bridge

Codex proof bodies, Qoder route/coefficient guidance.
[需人工审查] Actual Gaussian law, finite nonnegative sum and density integration.
-/
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal ComplexOrder
namespace JinWishart
noncomputable section

theorem actualCentralSquare_shiftedDeterminant_mean (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    ∫⁻ W, ENNReal.ofReal (W + (x : ℂ) • 1).det.re ∂complexWishart (m := n) (n := n) =
      ∑ S : Finset (Fin n), ENNReal.ofReal (x ^ (n - S.card)) *
        ENNReal.ofReal (((Nat.factorial n : ℕ) : ℝ) /
          ((Nat.factorial (n - S.card) : ℕ) : ℝ)) := by
  classical
  have hp : ∀ᵐ W ∂complexWishart (m := n) (n := n), W.PosSemidef :=
    (mem_ae_iff_prob_eq_one Matrix.posSemidef_is_closed.measurableSet).mpr
      complexWishart_measure_posSemidef
  have he : (∫⁻ W, ENNReal.ofReal (W + (x : ℂ) • 1).det.re ∂complexWishart (m := n) (n := n)) =
      ∫⁻ W, ∑ S : Finset (Fin n), ENNReal.ofReal (x ^ (n - S.card)) *
        ENNReal.ofReal (W.submatrix (Subtype.val : S → Fin n) (Subtype.val : S → Fin n)).det.re
          ∂complexWishart (m := n) (n := n) := by
    apply lintegral_congr_ae
    filter_upwards [hp] with W hW
    exact ofReal_det_add_scalar_eq_sum_principalMinors W hW x hx
  rw [he, lintegral_finsetSum _ (by intro S _; fun_prop)]
  apply Finset.sum_congr rfl
  intro S _
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, complexWishart_principalMinor_re_mean]

/-- Actual-law integration against the proven canonical matrix density. -/
theorem lintegral_complexWishart_eq_cone (d n : ℕ)
    (f : Matrix (Fin n) (Fin n) ℂ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ W, f W ∂complexWishart (m := d + n) (n := n) =
      ENNReal.ofReal (centralWishartDensityConstant d n) *
        ∫⁻ q in centralCoordinatePositiveCone n,
          f (hermitianOfRealCoordinates q) * ENNReal.ofReal
            (centralConeWeight d (hermitianOfRealCoordinates q)) ∂hermitianRealCoordinateMeasure n := by
  classical
  have hH := continuous_hermitianOfRealCoordinates (n := n) |>.measurable
  rw [complexWishart_eq_map_closedDensity, lintegral_map hf hH,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_centralWishartCoordinateDensity d n)
      (show Measurable (fun q => f (hermitianOfRealCoordinates q)) from hf.comp hH),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_indicator (measurableSet_centralCoordinatePositiveCone n)]
  apply lintegral_congr
  intro q
  simp only [Pi.mul_apply]
  by_cases hq : q ∈ centralCoordinatePositiveCone n
  · rw [Set.indicator_of_mem hq, centralWishartCoordinateDensity_on_cone d n q hq]
    ring
  · rw [Set.indicator_of_notMem hq]
    have hd : centralWishartCoordinateDensity d n q = 0 := if_neg hq
    rw [hd, zero_mul]

theorem centralWishartDensityConstant_one_surplus (n : ℕ) :
    centralWishartDensityConstant 1 n = centralWishartDensityConstant 0 n /
      ((Nat.factorial n : ℕ) : ℝ) := by
  induction n with
  | zero => simp [centralWishartDensityConstant]
  | succ n ih =>
      rw [centralWishartDensityConstant_succ, centralWishartDensityConstant_succ, ih]
      simp only [Nat.zero_add, Nat.one_add]
      have hn : ((Nat.factorial n : ℕ) : ℝ) ≠ 0 := by positivity
      have hs : ((Nat.factorial (n + 1) : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp

end
end JinWishart

#print axioms JinWishart.actualCentralSquare_shiftedDeterminant_mean
#print axioms JinWishart.lintegral_complexWishart_eq_cone
#print axioms JinWishart.centralWishartDensityConstant_one_surplus
