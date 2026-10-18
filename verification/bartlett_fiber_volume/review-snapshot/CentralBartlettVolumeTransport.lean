import JinWishartFormalization.CentralBartlettFiberVolume

/-!
# Positive-pivot Bartlett change of volume in all dimensions

Codex proofs. Tonelli combines the already proved fixed-pivot volume formula
over the actual real positive pivot coordinate. The weight r^n cancels r^-n.
Coordinates are explicitly R x (C^n x R^(n*n)), not ambient complex-matrix
Lebesgue measure. Alignment with the full (n+1)^2 real matrix coordinate
permutation and the actual Wishart density induction remains separate.
[需人工审查] Tonelli, restrictions, reference measures and later model use.
-/

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace JinWishart
noncomputable section

def centralBartlettVolumeMap {n : ℕ}
    (p : ℝ × (EuclideanSpace ℂ (Fin n) × Matrix (Fin n) (Fin n) ℝ)) :=
  (p.1, centralBartlettVolumeFiber p.1 p.2)

theorem continuous_centralBartlettVolumeMap (n : ℕ) :
    Continuous (centralBartlettVolumeMap (n := n)) := by
  exact continuous_fst.prodMk
    ((continuous_fst.sqrt.smul continuous_snd.fst).prodMk
      (continuous_snd.snd.add ((continuous_centralBartlettResidualShift n).comp continuous_snd.fst)))

/-- General mixed-coordinate volume theorem, with forward Jacobian weight r^n. -/
theorem centralBartlettVolumeMap_weighted_volume (n : ℕ) :
    ((((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
      ((volume : Measure (EuclideanSpace ℂ (Fin n))).prod (hermitianRealCoordinateMeasure n))).withDensity
        (fun p => ENNReal.ofReal (p.1 ^ n))).map centralBartlettVolumeMap =
      ((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
        ((volume : Measure (EuclideanSpace ℂ (Fin n))).prod (hermitianRealCoordinateMeasure n)) := by
  let ν := (volume : Measure (EuclideanSpace ℂ (Fin n))).prod (hermitianRealCoordinateMeasure n)
  let μ := (volume : Measure ℝ).restrict (Set.Ioi 0)
  have hF := (continuous_centralBartlettVolumeMap n).measurable
  apply Measure.ext_of_lintegral
  intro f hf
  have hfixed (r : ℝ) (hr : 0 < r) :
      (∫⁻ p, f (r, centralBartlettVolumeFiber r p) ∂ν) =
        ENNReal.ofReal ((r ^ n)⁻¹) * ∫⁻ p, f (r, p) ∂ν := by
    have hfr : Measurable (fun p => f (r, p)) := hf.comp (measurable_const.prodMk measurable_id)
    rw [← lintegral_map hfr
      (continuous_centralBartlettVolumeFiber n r).measurable,
      centralBartlettVolumeFiber_map_volume n r hr, lintegral_smul_measure]
    rfl
  change (∫⁻ p, f p ∂Measure.map centralBartlettVolumeMap
    ((μ.prod ν).withDensity (fun p => ENNReal.ofReal (p.1 ^ n)))) = ∫⁻ p, f p ∂μ.prod ν
  rw [lintegral_map hf hF]
  rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop)
    (show Measurable (fun p => f (centralBartlettVolumeMap p)) from hf.comp hF)]
  rw [lintegral_prod _ (by fun_prop), lintegral_prod _ hf.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  change 0 < r at hr
  change (∫⁻ p, ENNReal.ofReal (r ^ n) * f (r, centralBartlettVolumeFiber r p) ∂ν) = _
  have hfr : Measurable (fun p => f (r, centralBartlettVolumeFiber r p)) :=
    hf.comp (measurable_const.prodMk (continuous_centralBartlettVolumeFiber n r).measurable)
  rw [lintegral_const_mul _ hfr, hfixed r hr,
    ← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hr.le n),
    mul_inv_cancel₀ (ne_of_gt (pow_pos hr n)), ENNReal.ofReal_one, one_mul]

end
end JinWishart

#print axioms JinWishart.continuous_centralBartlettVolumeMap
#print axioms JinWishart.centralBartlettVolumeMap_weighted_volume
