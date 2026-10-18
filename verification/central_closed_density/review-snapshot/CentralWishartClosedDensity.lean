import JinWishartFormalization.CentralWishartDensityAlgebra
import JinWishartFormalization.CentralBartlettDensityTransport

/-!
# Actual central Wishart determinant/trace density

Codex proofs. Variance-one complex entries and canonical n^2 real coordinates.
[需人工审查] Actual-law induction, finite product measures and cone restriction.
-/
open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal ComplexOrder
namespace JinWishart
noncomputable section

theorem centralWishartCoordinateDensity_bartlett (d n : ℕ) (r : ℝ) (hr : 0 < r)
    (z : EuclideanSpace ℂ (Fin n)) (Q : Matrix (Fin n) (Fin n) ℝ) :
    gammaPDF ((d + n + 1 : ℕ) : ℝ) 1 r *
      (ENNReal.ofReal ((Real.pi⁻¹) ^ n * Real.exp (-‖z‖ ^ 2)) *
        centralWishartCoordinateDensity d n Q) =
      ENNReal.ofReal (r ^ n) * centralWishartCoordinateDensity d (n + 1)
        (centralBartlettCoordinateChart (r, (z, Q))) := by
  classical
  unfold centralWishartCoordinateDensity
  rw [hermitianOfRealCoordinates_centralChart]
  by_cases hQ : (hermitianOfRealCoordinates Q).PosDef
  · rw [if_pos hQ, if_pos ((centralBartlettGram_posDef_iff r hr z _).mpr hQ),
      gammaPDF_nat_succ_positive (d + n) r hr, centralBartlettGram_det r hr, centralBartlettGram_trace]
    have hd : 0 ≤ (hermitianOfRealCoordinates Q).det.re :=
      (Complex.nonneg_iff.mp hQ.det_pos.le).1
    have hK := (centralWishartDensityConstant_pos d n).le
    have hf : 0 ≤ (((Nat.factorial (d + n) : ℕ) : ℝ)⁻¹ * r ^ (d + n) * Real.exp (-r)) := by positivity
    have hc : 0 ≤ (Real.pi⁻¹) ^ n * Real.exp (-‖z‖ ^ 2) := by positivity
    rw [← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_mul hf, ← ENNReal.ofReal_mul (pow_nonneg hr.le n)]
    congr 1
    have hn : ((‖z‖ : ℂ) ^ 2).re = ‖z‖ ^ 2 := by norm_cast
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.add_re, hn, centralWishartDensityConstant_succ]
    rw [pow_add, mul_pow]
    have he : Real.exp (-r) * Real.exp (-‖z‖ ^ 2) *
        Real.exp (-(hermitianOfRealCoordinates Q).trace.re) =
        Real.exp (-(r + ‖z‖ ^ 2 + (hermitianOfRealCoordinates Q).trace.re)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    calc
      _ = ((Real.pi⁻¹) ^ n * centralWishartDensityConstant d n *
          ((Nat.factorial (d + n) : ℕ) : ℝ)⁻¹ * r ^ n * r ^ d *
          (hermitianOfRealCoordinates Q).det.re ^ d) *
          (Real.exp (-r) * Real.exp (-‖z‖ ^ 2) * Real.exp (-(hermitianOfRealCoordinates Q).trace.re)) := by ring
      _ = _ := by rw [he]; ring
  · rw [if_neg hQ, if_neg (by simpa only [centralBartlettGram_posDef_iff r hr z _] using hQ)]
    simp

theorem gammaMeasure_nat_succ_eq_positive_density (k : ℕ) :
    gammaMeasure ((k + 1 : ℕ) : ℝ) 1 =
      ((volume : Measure ℝ).restrict (Set.Ioi 0)).withDensity
        (gammaPDF ((k + 1 : ℕ) : ℝ) 1) := by
  have hp : ∀ᵐ r ∂gammaMeasure ((k + 1 : ℕ) : ℝ) 1, r ∈ Set.Ioi 0 :=
    (gammaMeasure_nat_succ_absolutelyContinuous_positive k).ae_le
      (ae_restrict_mem measurableSet_Ioi)
  rw [← restrict_withDensity measurableSet_Ioi]
  exact (Measure.restrict_eq_self_of_ae_mem hp).symm

theorem centralWishartCoordinateDensity_restrict_pivot (d n : ℕ) :
    ((hermitianRealCoordinateMeasure (n + 1)).restrict {q | 0 < q 0 0}).withDensity
        (centralWishartCoordinateDensity d (n + 1)) =
      (hermitianRealCoordinateMeasure (n + 1)).withDensity
        (centralWishartCoordinateDensity d (n + 1)) := by
  classical
  rw [← withDensity_indicator (by measurability)]
  congr 1
  funext q
  by_cases hp : 0 < q 0 0
  · exact Set.indicator_of_mem (show q ∈ {q | 0 < q 0 0} from hp) _
  · rw [Set.indicator_of_notMem (show q ∉ {q | 0 < q 0 0} from hp)]
    symm
    unfold centralWishartCoordinateDensity
    apply if_neg
    intro h
    have hdiag := h.diag_pos (i := (0 : Fin (n + 1)))
    apply hp
    simpa [hermitianOfRealCoordinates] using hdiag

/-- Closed density of the ACTUAL central rectangular Gram law, all row surpluses. -/
theorem complexWishart_realCoordinates_eq_closedDensity (d n : ℕ) :
    (complexWishart (m := d + n) (n := n)).map realCoordinatesOfHermitian =
      (hermitianRealCoordinateMeasure n).withDensity (centralWishartCoordinateDensity d n) := by
  induction n with
  | zero =>
      have hconst : (realCoordinatesOfHermitian (n := 0)) =
          fun _ => (0 : Matrix (Fin 0) (Fin 0) ℝ) := by
        funext A
        exact Subsingleton.elim _ _
      have hvol : hermitianRealCoordinateMeasure 0 =
          Measure.dirac (0 : Matrix (Fin 0) (Fin 0) ℝ) := Measure.pi_of_empty _ _
      have hd : centralWishartCoordinateDensity d 0 = fun _ => 1 := by
        funext q
        have hq : hermitianOfRealCoordinates q = (1 : Matrix (Fin 0) (Fin 0) ℂ) :=
          Subsingleton.elim _ _
        simp [centralWishartCoordinateDensity, hq, Matrix.PosDef.one,
          centralWishartDensityConstant]
      rw [hconst, Measure.map_const, measure_univ, one_smul, hd]
      simpa only [withDensity_const, one_smul] using hvol.symm
  | succ n ih =>
      rw [show d + (n + 1) = (d + n) + 1 by omega,
        complexWishart_realCoordinates_bartlett_recursion, ih,
        standardComplexColumnLaw_eq_withDensity, gammaMeasure_nat_succ_eq_positive_density]
      have hC : Measurable (fun z : EuclideanSpace ℂ (Fin n) =>
          ENNReal.ofReal ((Real.pi⁻¹) ^ n * Real.exp (-‖z‖ ^ 2))) := by fun_prop
      have hD := measurable_centralWishartCoordinateDensity d n
      have hG : Measurable (gammaPDF ((d + n + 1 : ℕ) : ℝ) 1) :=
        ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal _ _)
      have hCG : Measurable (fun p : EuclideanSpace ℂ (Fin n) × Matrix (Fin n) (Fin n) ℝ =>
          ENNReal.ofReal ((Real.pi⁻¹) ^ n * Real.exp (-‖p.1‖ ^ 2)) *
            centralWishartCoordinateDensity d n p.2) :=
        (hC.comp measurable_fst).mul (hD.comp measurable_snd)
      rw [prod_withDensity hC hD, prod_withDensity hG hCG]
      have hi :
          ((((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
            ((volume : Measure (EuclideanSpace ℂ (Fin n))).prod (hermitianRealCoordinateMeasure n))).withDensity
              (fun p => gammaPDF ((d + n + 1 : ℕ) : ℝ) 1 p.1 *
                (ENNReal.ofReal ((Real.pi⁻¹) ^ n * Real.exp (-‖p.2.1‖ ^ 2)) *
                  centralWishartCoordinateDensity d n p.2.2))) =
          ((((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
            ((volume : Measure (EuclideanSpace ℂ (Fin n))).prod (hermitianRealCoordinateMeasure n))).withDensity
              (fun p => ENNReal.ofReal (p.1 ^ n) *
                centralWishartCoordinateDensity d (n + 1) (centralBartlettCoordinateChart p))) := by
        apply withDensity_congr_ae
        have hp : ∀ᵐ p ∂((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
            ((volume : Measure (EuclideanSpace ℂ (Fin n))).prod (hermitianRealCoordinateMeasure n)), 0 < p.1 := by
          apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
          exact ae_of_all _ (fun _ => hr)
        filter_upwards [hp] with p hp
        exact centralWishartCoordinateDensity_bartlett d n p.1 hp p.2.1 p.2.2
      rw [hi, centralBartlettCoordinateChart_weighted_density n _
        (measurable_centralWishartCoordinateDensity d (n + 1)),
        centralWishartCoordinateDensity_restrict_pivot]

theorem complexWishart_realCoordinates_eq_closedDensity_of_le (t s : ℕ) (hst : s ≤ t) :
    (complexWishart (m := t) (n := s)).map realCoordinatesOfHermitian =
      (hermitianRealCoordinateMeasure s).withDensity (centralWishartCoordinateDensity (t - s) s) := by
  simpa only [Nat.sub_add_cancel hst] using complexWishart_realCoordinates_eq_closedDensity (t - s) s

/-- Normalization is a consequence of the actual probability law, not a premise. -/
theorem lintegral_centralWishartCoordinateDensity (d n : ℕ) :
    ∫⁻ q, centralWishartCoordinateDensity d n q ∂hermitianRealCoordinateMeasure n = 1 := by
  have h := congrArg (fun μ : Measure (Matrix (Fin n) (Fin n) ℝ) => μ Set.univ)
    (complexWishart_realCoordinates_eq_closedDensity d n)
  simpa only [Measure.map_apply_of_aemeasurable
    (continuous_realCoordinatesOfHermitian.measurable.aemeasurable) MeasurableSet.univ,
    Set.preimage_univ, measure_univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] using h.symm

end
end JinWishart

#print axioms JinWishart.centralWishartCoordinateDensity_bartlett
#print axioms JinWishart.gammaMeasure_nat_succ_eq_positive_density
#print axioms JinWishart.centralWishartCoordinateDensity_restrict_pivot
#print axioms JinWishart.complexWishart_realCoordinates_eq_closedDensity
#print axioms JinWishart.complexWishart_realCoordinates_eq_closedDensity_of_le
#print axioms JinWishart.lintegral_centralWishartCoordinateDensity
