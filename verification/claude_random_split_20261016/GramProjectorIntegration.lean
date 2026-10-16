import JinWishartFormalization.GaussianGramProjector
import JinWishartFormalization.GaussianRandomSubspaceLaw

/-! Interface integration check only, not a new actual Wishart theorem.
Full-rank probability and constant dimensions have not been established here.
[需人工审查] Measure/model correspondence and almost-everywhere rank assumptions. -/

open MeasureTheory ProbabilityTheory

noncomputable section

example (m n : ℕ) (μ : Measure (Matrix (Fin m) (Fin n) ℂ)) [SFinite μ]
    (k l : ℕ) (hk : 0 < k) (hl : 0 < l)
    (hK : ∀ᵐ A ∂μ, Module.finrank ℝ (JinWishart.totalGramColumnSpaceReal A) = 2 * k)
    (hC : ∀ᵐ A ∂μ, Module.finrank ℝ (JinWishart.totalGramColumnSpaceReal A)ᗮ = 2 * l) :
    (μ.prod (stdGaussian (EuclideanSpace ℂ (Fin m)))).map
      (fun p => (p.1, JinWishart.gaussianSplitEnergy
        (JinWishart.totalGramColumnSpaceReal p.1) p.2)) =
      μ.prod ((gammaMeasure (k : ℝ) 1).prod (gammaMeasure (l : ℝ) 1)) := by
  exact JinWishart.stdGaussian_random_split_energy_law μ
    JinWishart.totalGramColumnSpaceReal
    (JinWishart.measurable_totalGramColumnSpaceReal_projection m n) k l hk hl hK hC
