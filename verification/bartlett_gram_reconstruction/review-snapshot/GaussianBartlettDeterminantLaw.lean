import JinWishartFormalization.GaussianBartlettGramDeterminant

/-!
# Actual central Wishart determinant recursion

Codex proof. The first Gamma energy is independent of an actual smaller
Wishart matrix. This uses the full Bartlett block law, with no density premise.
Valid also for singular rectangular residuals and the empty residual matrix.
[需人工审查] Almost-everywhere transport, product measures, CN variance/model.
-/

open Matrix MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

/-- Distributional determinant recursion: an independent Gamma(m+1,rate1)
times the determinant of actual Wishart(m,n). No spectral density is used. -/
theorem complexWishart_det_bartlett_recursion (m n : ℕ) :
    (complexWishart (m := m + 1) (n := n + 1)).map Matrix.det =
      ((gammaMeasure ((m + 1 : ℕ) : ℝ) 1).prod
        (complexWishart (m := m) (n := n))).map
          (fun p => (p.1 : ℂ) * p.2.det) := by
  letI : IsProbabilityMeasure (gammaMeasure ((m + 1 : ℕ) : ℝ) 1) :=
    isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
  have hr : ∀ᵐ r ∂gammaMeasure ((m + 1 : ℕ) : ℝ) 1, 0 < r := by
    rw [← standardComplexColumnLaw_norm_sq_law (m + 1) (Nat.succ_pos m),
      ae_map_iff (by fun_prop) measurableSet_Ioi]
    filter_upwards [standardComplexColumnLaw_nonzero_ae (m + 1) (Nat.succ_pos m)] with u hu
    exact sq_pos_of_pos (norm_pos_iff.mpr hu)
  have hprod : ∀ᵐ p ∂(gammaMeasure ((m + 1 : ℕ) : ℝ) 1).prod
      ((standardComplexColumnLaw n).prod (complexWishart (m := m) (n := n))), 0 < p.1 := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
    filter_upwards [hr] with r hr using ae_of_all _ (fun _ => hr)
  rw [complexWishart_centralBartlett_recursion,
    Measure.map_map (by fun_prop) (continuous_centralBartlettGram n).measurable]
  have heq : (fun p : ℝ × (EuclideanSpace ℂ (Fin n) × Matrix (Fin n) (Fin n) ℂ) =>
      (centralBartlettGram p.1 p.2.1 p.2.2).det) =ᵐ[
      (gammaMeasure ((m + 1 : ℕ) : ℝ) 1).prod
        ((standardComplexColumnLaw n).prod (complexWishart (m := m) (n := n)))]
      (fun p => (p.1 : ℂ) * p.2.2.det) := by
    filter_upwards [hprod] with p hp
    exact centralBartlettGram_det p.1 hp p.2.1 p.2.2
  change Measure.map (fun p : ℝ × (EuclideanSpace ℂ (Fin n) × Matrix (Fin n) (Fin n) ℂ) =>
    (centralBartlettGram p.1 p.2.1 p.2.2).det) _ = _
  rw [Measure.map_congr heq]
  have hdrop : ((gammaMeasure ((m + 1 : ℕ) : ℝ) 1).prod
      ((standardComplexColumnLaw n).prod (complexWishart (m := m) (n := n)))).map
      (Prod.map id Prod.snd) =
      (gammaMeasure ((m + 1 : ℕ) : ℝ) 1).prod (complexWishart (m := m) (n := n)) := by
    rw [← Measure.map_prod_map _ _ measurable_id measurable_snd, Measure.map_id,
      Measure.map_snd_prod, measure_univ, one_smul]
  rw [← hdrop, Measure.map_map (by fun_prop) (measurable_id.prodMap measurable_snd)]
  rfl

end
end JinWishart

#print axioms JinWishart.complexWishart_det_bartlett_recursion
