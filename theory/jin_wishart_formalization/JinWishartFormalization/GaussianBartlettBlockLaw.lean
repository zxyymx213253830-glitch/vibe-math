import JinWishartFormalization.GaussianBartlettFiber

/-!
# The actual joint central Bartlett matrix block law, arbitrary dimensions

Codex proofs. The full normalized coefficient vector AND residual Gram have
a constant fixed-column law; joint measurability is explicit, so skew_product
combines fibers without a measurable choice of unitary frames. No candidate
matrix/spectral density is assumed. [需人工审查] Skew-product/null-set transport,
variance, and the eventual block-to-Gram coordinate interpretation.
-/

open Matrix MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

theorem standardComplexColumnLaw_norm_sq_law (m : ℕ) (hm : 0 < m) :
    (standardComplexColumnLaw m).map (fun u => ‖u‖ ^ 2) = gammaMeasure (m : ℝ) 1 := by
  have h := stdGaussian_half_norm_sq_law (E := EuclideanSpace ℂ (Fin m)) m hm
    (by rw [finrank_real_of_complex, finrank_euclideanSpace_fin])
  have hs : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hnorm (v : EuclideanSpace ℂ (Fin m)) :
      ‖(Real.sqrt (2 : ℝ))⁻¹ • v‖ ^ 2 = ‖v‖ ^ 2 / 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs), mul_pow,
      inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  unfold standardComplexColumnLaw
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  simpa only [Function.comp_def, hnorm] using h

theorem standardComplexColumnLaw_nonzero_ae (m : ℕ) (hm : 0 < m) :
    ∀ᵐ u ∂standardComplexColumnLaw m, u ≠ 0 := by
  have hg0 : gammaMeasure (m : ℝ) 1 ({0} : Set ℝ) = 0 := by simp [gammaMeasure]
  rw [← standardComplexColumnLaw_norm_sq_law m hm,
    Measure.map_apply (by fun_prop) (measurableSet_singleton _)] at hg0
  rw [ae_iff]
  simpa [Set.preimage, sq_eq_zero_iff] using hg0

/-- Entire first column and full residual-Gram fiber separate jointly. -/
theorem centralBartlett_product_law (m n : ℕ) :
    ((standardComplexColumnLaw (m + 1)).prod
      (complexGaussianMatrixLaw (0 : Matrix (Fin (m + 1)) (Fin n) ℂ))).map
      (fun p => (‖p.1‖ ^ 2, centralBartlettFiber p.1 p.2)) =
      (gammaMeasure ((m + 1 : ℕ) : ℝ) 1).prod
        ((standardComplexColumnLaw n).prod (complexWishart (m := m) (n := n))) := by
  have hNorm : MeasurePreserving (fun u : EuclideanSpace ℂ (Fin (m + 1)) => ‖u‖ ^ 2)
      (standardComplexColumnLaw (m + 1)) (gammaMeasure ((m + 1 : ℕ) : ℝ) 1) :=
    ⟨by fun_prop, standardComplexColumnLaw_norm_sq_law (m + 1) (Nat.succ_pos m)⟩
  have hFiber : ∀ᵐ u ∂standardComplexColumnLaw (m + 1),
      (complexGaussianMatrixLaw (0 : Matrix (Fin (m + 1)) (Fin n) ℂ)).map
        (centralBartlettFiber u) =
        (standardComplexColumnLaw n).prod (complexWishart (m := m) (n := n)) := by
    filter_upwards [standardComplexColumnLaw_nonzero_ae (m + 1) (Nat.succ_pos m)] with u hu
    exact centralBartlettFiber_law u hu
  exact (hNorm.skew_product (measurable_centralBartlettFiber m n) hFiber).map_eq

def centralBartlettCoordinates {m n : ℕ} (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℂ) :
    ℝ × (EuclideanSpace ℂ (Fin n) × Matrix (Fin n) (Fin n) ℂ) :=
  let p := matrixColumnSplit A
  (‖p.1‖ ^ 2, centralBartlettFiber p.1 p.2)

/-- Actual central Gaussian [u,V] -> (||u||^2, normalized inner products,
residual Gram) has Gamma x CN x lower-row Wishart law, not just marginals. -/
theorem actualCentralBartlett_block_law (m n : ℕ) :
    (complexGaussianMatrixLaw (0 : Matrix (Fin (m + 1)) (Fin (n + 1)) ℂ)).map
      centralBartlettCoordinates =
      (gammaMeasure ((m + 1 : ℕ) : ℝ) 1).prod
        ((standardComplexColumnLaw n).prod (complexWishart (m := m) (n := n))) := by
  have hF : Measurable (fun p : EuclideanSpace ℂ (Fin (m + 1)) ×
      Matrix (Fin (m + 1)) (Fin n) ℂ => (‖p.1‖ ^ 2, centralBartlettFiber p.1 p.2)) :=
    (measurable_fst.norm.pow_const 2).prodMk (measurable_centralBartlettFiber m n)
  change (complexGaussianMatrixLaw (0 : Matrix (Fin (m + 1)) (Fin (n + 1)) ℂ)).map
    ((fun p => (‖p.1‖ ^ 2, centralBartlettFiber p.1 p.2)) ∘ matrixColumnSplit) = _
  rw [← Measure.map_map hF (measurable_matrixColumnSplit (m + 1) n),
    complexGaussianMatrixLaw_columnSplit, centralBartlett_product_law]

end
end JinWishart

#print axioms JinWishart.standardComplexColumnLaw_norm_sq_law
#print axioms JinWishart.standardComplexColumnLaw_nonzero_ae
#print axioms JinWishart.centralBartlett_product_law
#print axioms JinWishart.actualCentralBartlett_block_law
