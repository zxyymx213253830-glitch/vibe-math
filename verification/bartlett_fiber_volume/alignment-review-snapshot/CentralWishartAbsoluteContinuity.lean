import JinWishartFormalization.CentralBartlettCoordinateJacobian
import JinWishartFormalization.GaussianComplexColumnDensity

/-!
# Actual central complex Wishart is absolutely continuous in Hermitian coordinates

Codex proofs. Induct on the number of columns using the ACTUAL Bartlett block
law and the general coordinate-volume theorem. No target density is a premise.
The reference measure is exactly the nested n^2-real-coordinate Pi Lebesgue
measure. This establishes absolute continuity, not the closed determinant/trace
density or a joint spectral density. [需人工审查] Null-set transport, finite
products, variance, and correspondence with the paper model.
-/

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal ComplexOrder
namespace JinWishart
noncomputable section

theorem centralBartlettCoordinateChart_quasiMeasurePreserving (n : ℕ) :
    Measure.QuasiMeasurePreserving (centralBartlettCoordinateChart (n := n))
      (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
        ((volume : Measure (EuclideanSpace ℂ (Fin n))).prod (hermitianRealCoordinateMeasure n)))
      (hermitianRealCoordinateMeasure (n + 1)) := by
  let μ := ((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
    ((volume : Measure (EuclideanSpace ℂ (Fin n))).prod (hermitianRealCoordinateMeasure n))
  have hF : Measurable (centralBartlettCoordinateChart (n := n)) :=
    (hermitianBlockCoordinateEquiv n).symm.measurable.comp
      (continuous_centralBartlettVolumeMap n).measurable
  have hw : Measurable (fun p : ℝ × (EuclideanSpace ℂ (Fin n) × Matrix (Fin n) (Fin n) ℝ) =>
      ENNReal.ofReal (p.1 ^ n)) := by fun_prop
  have hp : ∀ᵐ p ∂μ, ENNReal.ofReal (p.1 ^ n) ≠ 0 := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact ae_of_all _ (fun _ => ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos hr n)))
  have hmp : MeasurePreserving centralBartlettCoordinateChart
      (μ.withDensity (fun p => ENNReal.ofReal (p.1 ^ n)))
      ((hermitianRealCoordinateMeasure (n + 1)).restrict {q | 0 < q 0 0}) :=
    ⟨hF, centralBartlettCoordinateChart_weighted_volume n⟩
  exact (hmp.quasiMeasurePreserving.mono_left
    (withDensity_absolutelyContinuous' hw.aemeasurable hp)).mono_right
      Measure.absolutelyContinuous_restrict

/-- Entire actual Gram law in the canonical real coordinate block chart. -/
theorem complexWishart_realCoordinates_bartlett_recursion (m n : ℕ) :
    (complexWishart (m := m + 1) (n := n + 1)).map realCoordinatesOfHermitian =
      ((gammaMeasure ((m + 1 : ℕ) : ℝ) 1).prod
        ((standardComplexColumnLaw n).prod
          ((complexWishart (m := m) (n := n)).map realCoordinatesOfHermitian))).map
            centralBartlettCoordinateChart := by
  let γ := gammaMeasure ((m + 1 : ℕ) : ℝ) 1
  let C := standardComplexColumnLaw n
  let W := complexWishart (m := m) (n := n)
  letI : IsProbabilityMeasure γ := isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
  have hR := (continuous_realCoordinatesOfHermitian (n := n)).measurable
  have hchart : Measurable (centralBartlettCoordinateChart (n := n)) :=
    (hermitianBlockCoordinateEquiv n).symm.measurable.comp
      (continuous_centralBartlettVolumeMap n).measurable
  have hinner : (C.prod W).map (Prod.map id realCoordinatesOfHermitian) =
      C.prod (W.map realCoordinatesOfHermitian) := by
    rw [← Measure.map_prod_map _ _ measurable_id hR, Measure.map_id]
  have houter : (γ.prod (C.prod W)).map (Prod.map id (Prod.map id realCoordinatesOfHermitian)) =
      γ.prod (C.prod (W.map realCoordinatesOfHermitian)) := by
    rw [← Measure.map_prod_map _ _ measurable_id (measurable_id.prodMap hR),
      Measure.map_id, hinner]
  have hPSD : ∀ᵐ B ∂W, B.PosSemidef :=
    (mem_ae_iff_prob_eq_one Matrix.posSemidef_is_closed.measurableSet).mpr complexWishart_measure_posSemidef
  have hproj : MeasurePreserving
      (fun p : ℝ × (EuclideanSpace ℂ (Fin n) × Matrix (Fin n) (Fin n) ℂ) => p.2.2)
      (γ.prod (C.prod W)) W :=
    (measurePreserving_snd (μ := C) (ν := W)).comp
      (measurePreserving_snd (μ := γ) (ν := C.prod W))
  have hB := hproj.quasiMeasurePreserving.ae hPSD
  rw [complexWishart_centralBartlett_recursion,
    Measure.map_map (continuous_realCoordinatesOfHermitian (n := n + 1)).measurable
      (continuous_centralBartlettGram n).measurable]
  change Measure.map _ (γ.prod (C.prod W)) = _
  rw [← houter, Measure.map_map hchart (measurable_id.prodMap (measurable_id.prodMap hR))]
  apply Measure.map_congr
  filter_upwards [hB] with p hp
  change realCoordinatesOfHermitian (centralBartlettGram p.1 p.2.1 p.2.2) =
    centralBartlettCoordinateChart (p.1, (p.2.1, realCoordinatesOfHermitian p.2.2))
  rw [centralBartlettCoordinateChart_eq_realGram,
    hermitianOfRealCoordinates_realCoordinates _ hp.isHermitian]

theorem gammaMeasure_nat_succ_absolutelyContinuous_positive (m : ℕ) :
    gammaMeasure ((m + 1 : ℕ) : ℝ) 1 ≪ (volume : Measure ℝ).restrict (Set.Ioi 0) := by
  have hv : gammaMeasure ((m + 1 : ℕ) : ℝ) 1 ≪ (volume : Measure ℝ) :=
    withDensity_absolutelyContinuous _ _
  have hp : ∀ᵐ r ∂gammaMeasure ((m + 1 : ℕ) : ℝ) 1, r ∈ Set.Ioi 0 := by
    change ∀ᵐ r ∂gammaMeasure ((m + 1 : ℕ) : ℝ) 1, 0 < r
    rw [← standardComplexColumnLaw_norm_sq_law (m + 1) (Nat.succ_pos m),
      ae_map_iff (by fun_prop) measurableSet_Ioi]
    filter_upwards [standardComplexColumnLaw_nonzero_ae (m + 1) (Nat.succ_pos m)] with u hu
    exact sq_pos_of_pos (norm_pos_iff.mpr hu)
  simpa only [Measure.restrict_eq_self_of_ae_mem hp] using hv.restrict (Set.Ioi 0)

/-- General actual CENTRAL full-dimensional absolute continuity, row surplus d. -/
theorem complexWishart_realCoordinates_absolutelyContinuous (d n : ℕ) :
    (complexWishart (m := d + n) (n := n)).map realCoordinatesOfHermitian ≪
      hermitianRealCoordinateMeasure n := by
  induction n with
  | zero =>
      have hconst : (realCoordinatesOfHermitian (n := 0)) =
          fun _ => (0 : Matrix (Fin 0) (Fin 0) ℝ) := by
        funext A
        exact Subsingleton.elim _ _
      have hvol : hermitianRealCoordinateMeasure 0 =
          Measure.dirac (0 : Matrix (Fin 0) (Fin 0) ℝ) := by
        exact Measure.pi_of_empty _ _
      rw [hconst, Measure.map_const, measure_univ, one_smul, hvol]
  | succ n ih =>
      have hC : standardComplexColumnLaw n ≪ (volume : Measure (EuclideanSpace ℂ (Fin n))) := by
        rw [standardComplexColumnLaw_eq_withDensity]
        exact withDensity_absolutelyContinuous _ _
      have hinput := (gammaMeasure_nat_succ_absolutelyContinuous_positive (d + n)).prod (hC.prod ih)
      have hmap := (centralBartlettCoordinateChart_quasiMeasurePreserving n).mono_left hinput
      rw [show d + (n + 1) = (d + n) + 1 by omega,
        complexWishart_realCoordinates_bartlett_recursion]
      exact hmap.absolutelyContinuous

theorem complexWishart_realCoordinates_absolutelyContinuous_of_le (t s : ℕ) (hst : s ≤ t) :
    (complexWishart (m := t) (n := s)).map realCoordinatesOfHermitian ≪
      hermitianRealCoordinateMeasure s := by
  simpa only [Nat.sub_add_cancel hst] using complexWishart_realCoordinates_absolutelyContinuous (t - s) s

end
end JinWishart

#print axioms JinWishart.centralBartlettCoordinateChart_quasiMeasurePreserving
#print axioms JinWishart.complexWishart_realCoordinates_bartlett_recursion
#print axioms JinWishart.gammaMeasure_nat_succ_absolutelyContinuous_positive
#print axioms JinWishart.complexWishart_realCoordinates_absolutelyContinuous
#print axioms JinWishart.complexWishart_realCoordinates_absolutelyContinuous_of_le
