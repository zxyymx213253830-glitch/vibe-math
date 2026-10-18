import JinWishartFormalization.CentralWishartAbsoluteContinuity

/-!
# Density transport through the general positive Bartlett chart

Codex proofs. The function f below is arbitrary Lebesgue input data, not an
assumption of the desired actual Wishart density. Subsequent probability
induction must supply f from the actual Gamma/CN/lower-size law.
[需人工审查] Inverse chart, restrictions and nonnegative integral transport.
-/

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace JinWishart
noncomputable section

theorem measurable_centralBartlettCoordinateChart (n : ℕ) :
    Measurable (centralBartlettCoordinateChart (n := n)) :=
  (hermitianBlockCoordinateEquiv n).symm.measurable.comp
    (continuous_centralBartlettVolumeMap n).measurable

def centralBartlettCoordinateInverse {n : ℕ} (q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    ℝ × (EuclideanSpace ℂ (Fin n) × Matrix (Fin n) (Fin n) ℝ) :=
  let p := hermitianBlockCoordinateEquiv n q
  (p.1, ((Real.sqrt p.1)⁻¹ • p.2.1,
    p.2.2 - centralBartlettResidualShift ((Real.sqrt p.1)⁻¹ • p.2.1)))

theorem measurable_centralBartlettCoordinateInverse (n : ℕ) :
    Measurable (centralBartlettCoordinateInverse (n := n)) := by
  let e := hermitianBlockCoordinateEquiv n
  have hs : Measurable (fun q => (Real.sqrt (e q).1)⁻¹ • (e q).2.1) := by fun_prop
  have hQ := measurable_snd.comp (measurable_snd.comp e.measurable)
  have hS := (continuous_centralBartlettResidualShift n).measurable.comp hs
  exact (measurable_fst.comp e.measurable).prodMk (hs.prodMk
    (Measurable.of_eval_matrix _ (fun i j =>
      (hQ.eval_matrix (i := i) (j := j)).sub (hS.eval_matrix (i := i) (j := j)))))

theorem centralBartlettCoordinateChart_left_inverse {n : ℕ}
    (p : ℝ × (EuclideanSpace ℂ (Fin n) × Matrix (Fin n) (Fin n) ℝ)) (hp : 0 < p.1) :
    centralBartlettCoordinateInverse (centralBartlettCoordinateChart p) = p := by
  simp [centralBartlettCoordinateInverse, centralBartlettCoordinateChart,
    centralBartlettVolumeMap, centralBartlettVolumeFiber, smul_smul,
    ne_of_gt (Real.sqrt_pos.mpr hp)]

theorem centralBartlettCoordinateChart_pivot {n : ℕ}
    (p : ℝ × (EuclideanSpace ℂ (Fin n) × Matrix (Fin n) (Fin n) ℝ)) :
    centralBartlettCoordinateChart p 0 0 = p.1 := by
  rw [centralBartlettCoordinateChart_eq_realGram]
  simp [realCoordinatesOfHermitian, centralBartlettGram]

theorem centralBartlettCoordinateChart_weighted_density (n : ℕ)
    (g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ → ℝ≥0∞) (hg : Measurable g) :
    ((((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
      ((volume : Measure (EuclideanSpace ℂ (Fin n))).prod (hermitianRealCoordinateMeasure n))).withDensity
        (fun p => ENNReal.ofReal (p.1 ^ n) * g (centralBartlettCoordinateChart p))).map
          centralBartlettCoordinateChart =
      ((hermitianRealCoordinateMeasure (n + 1)).restrict {q | 0 < q 0 0}).withDensity g := by
  let μ := ((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
    ((volume : Measure (EuclideanSpace ℂ (Fin n))).prod (hermitianRealCoordinateMeasure n))
  have hF := measurable_centralBartlettCoordinateChart n
  have hw : Measurable (fun p : ℝ × (EuclideanSpace ℂ (Fin n) × Matrix (Fin n) (Fin n) ℝ) =>
      ENNReal.ofReal (p.1 ^ n)) := by fun_prop
  have hmp : MeasurePreserving centralBartlettCoordinateChart
      (μ.withDensity (fun p => ENNReal.ofReal (p.1 ^ n)))
      ((hermitianRealCoordinateMeasure (n + 1)).restrict {q | 0 < q 0 0}) :=
    ⟨hF, centralBartlettCoordinateChart_weighted_volume n⟩
  rw [show (fun p => ENNReal.ofReal (p.1 ^ n) * g (centralBartlettCoordinateChart p)) =
      (fun p => ENNReal.ofReal (p.1 ^ n)) * (g ∘ centralBartlettCoordinateChart) from rfl,
    withDensity_mul _ hw (hg.comp hF)]
  ext s hs
  rw [Measure.map_apply hF hs, withDensity_apply _ (hs.preimage hF), withDensity_apply _ hs]
  exact hmp.setLIntegral_comp_preimage hs hg

theorem centralBartlettCoordinateChart_density_map (n : ℕ)
    (f : ℝ × (EuclideanSpace ℂ (Fin n) × Matrix (Fin n) (Fin n) ℝ) → ℝ≥0∞)
    (hf : Measurable f) :
    ((((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
      ((volume : Measure (EuclideanSpace ℂ (Fin n))).prod (hermitianRealCoordinateMeasure n))).withDensity f).map
          centralBartlettCoordinateChart =
      ((hermitianRealCoordinateMeasure (n + 1)).restrict {q | 0 < q 0 0}).withDensity
        (fun q => f (centralBartlettCoordinateInverse q) / ENNReal.ofReal ((q 0 0) ^ n)) := by
  let g := fun q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ =>
    f (centralBartlettCoordinateInverse q) / ENNReal.ofReal ((q 0 0) ^ n)
  have hg : Measurable g := (hf.comp (measurable_centralBartlettCoordinateInverse n)).div
    (by fun_prop)
  change _ = ((hermitianRealCoordinateMeasure (n + 1)).restrict {q | 0 < q 0 0}).withDensity g
  rw [← centralBartlettCoordinateChart_weighted_density n g hg]
  congr 1
  apply withDensity_congr_ae
  have hp : ∀ᵐ p ∂((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
      ((volume : Measure (EuclideanSpace ℂ (Fin n))).prod (hermitianRealCoordinateMeasure n)), 0 < p.1 := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact ae_of_all _ (fun _ => hr)
  filter_upwards [hp] with p hp
  dsimp only [g]
  rw [centralBartlettCoordinateChart_left_inverse p hp, centralBartlettCoordinateChart_pivot]
  exact (ENNReal.mul_div_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos hp n)))
    ENNReal.ofReal_ne_top).symm

end
end JinWishart

#print axioms JinWishart.measurable_centralBartlettCoordinateChart
#print axioms JinWishart.measurable_centralBartlettCoordinateInverse
#print axioms JinWishart.centralBartlettCoordinateChart_left_inverse
#print axioms JinWishart.centralBartlettCoordinateChart_pivot
#print axioms JinWishart.centralBartlettCoordinateChart_weighted_density
#print axioms JinWishart.centralBartlettCoordinateChart_density_map
