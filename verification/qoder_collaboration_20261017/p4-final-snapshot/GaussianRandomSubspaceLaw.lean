import JinWishartFormalization.GaussianOrthogonalSplitLaw
import Mathlib.MeasureTheory.Measure.Prod

/-!+# Gaussian energies in a random orthogonal splitting

Codex proofs. Two bounded local DeepSeek attempts on the fixed-fiber lemma were
not accepted (placeholder, then failed proof search). The complete targets,
responses and actual checker output are preserved separately. The final proof
below is a Codex completion, rather than an independently verified local proof.

The subspace may depend on arbitrary preceding data, independent of the fresh
Gaussian vector. Joint measurability of its ambient projection and almost-everywhere
constant even ranks are explicit premises. No target density is assumed.

[需人工审查] Skew-product/Fubini use, measurability and the eventual identification
of the preceding-column subspace in the actual Bartlett construction. These laws
do not yet prove a general QR/Bartlett matrix law or the general Wishart density.
-/

open MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- Fixed-fiber joint energy law, reusing the checked Gaussian splitting and
the existing radial Gamma laws without performing new radial integration. -/
theorem stdGaussian_orthogonal_energy_pair_law (K : Submodule ℝ E)
    (k l : ℕ) (hk : 0 < k) (hl : 0 < l)
    (hdimK : Module.finrank ℝ K = 2 * k)
    (hdimC : Module.finrank ℝ Kᗮ = 2 * l) :
    (stdGaussian E).map (fun z : E =>
      (‖K.orthogonalProjectionOnto z‖ ^ 2 / 2,
       ‖Kᗮ.orthogonalProjectionOnto z‖ ^ 2 / 2)) =
      (gammaMeasure (k : ℝ) 1).prod (gammaMeasure (l : ℝ) 1) := by
  have hi : IndepFun (fun z : E => ‖K.orthogonalProjectionOnto z‖ ^ 2 / 2)
      (fun z : E => ‖Kᗮ.orthogonalProjectionOnto z‖ ^ 2 / 2) (stdGaussian E) := by
    exact (stdGaussian_orthogonal_split_indep K).comp
      (φ := fun x : K => ‖x‖ ^ 2 / 2) (ψ := fun y : Kᗮ => ‖y‖ ^ 2 / 2)
      (by fun_prop) (by fun_prop)
  rw [hi.map_prod_eq_prod_map_map (by fun_prop) (by fun_prop),
    stdGaussian_projected_half_norm_sq_law K k hk hdimK,
    stdGaussian_projected_half_norm_sq_law Kᗮ l hl hdimC]

/-- Energies use the half-real-norm convention for the standard real Gaussian.
For complex CN(0,1) coordinates this is the usual complex squared norm. -/
def gaussianSplitEnergy (K : Submodule ℝ E) (z : E) : ℝ × ℝ :=
  (‖K.orthogonalProjectionOnto z‖ ^ 2 / 2,
   ‖Kᗮ.orthogonalProjectionOnto z‖ ^ 2 / 2)

theorem gaussianSplitEnergy_eq_ambient (K : Submodule ℝ E) (z : E) :
    gaussianSplitEnergy K z =
      (‖K.starProjection z‖ ^ 2 / 2, ‖z - K.starProjection z‖ ^ 2 / 2) := by
  rw [← K.starProjection_orthogonal_val z]
  rfl

variable {A : Type*} [MeasurableSpace A]

/-- No measurable choice of an orthonormal basis is used: measurability of the
ambient projector suffices for both energies, including the residual. -/
theorem measurable_gaussianSplitEnergy (K : A → Submodule ℝ E)
    (hproj : Measurable (fun p : A × E => (K p.1).starProjection p.2)) :
    Measurable (fun p : A × E => gaussianSplitEnergy (K p.1) p.2) := by
  simp_rw [gaussianSplitEnergy_eq_ambient]
  exact ((hproj.norm.pow_const 2).div_const 2).prodMk
    (((measurable_snd.sub hproj).norm.pow_const 2).div_const 2)

/-- The entire parameter and the two energies have a product law. Ranks may
fail on a null set (for example, a rank-deficient set of preceding columns). -/
theorem stdGaussian_random_split_energy_law (μ : Measure A) [SFinite μ]
    (K : A → Submodule ℝ E)
    (hproj : Measurable (fun p : A × E => (K p.1).starProjection p.2))
    (k l : ℕ) (hk : 0 < k) (hl : 0 < l)
    (hdimK : ∀ᵐ a ∂μ, Module.finrank ℝ (K a) = 2 * k)
    (hdimC : ∀ᵐ a ∂μ, Module.finrank ℝ (K a)ᗮ = 2 * l) :
    (μ.prod (stdGaussian E)).map (fun p : A × E =>
      (p.1, gaussianSplitEnergy (K p.1) p.2)) =
      μ.prod ((gammaMeasure (k : ℝ) 1).prod (gammaMeasure (l : ℝ) 1)) := by
  have hFiber : ∀ᵐ a ∂μ,
      (stdGaussian E).map (gaussianSplitEnergy (K a)) =
        (gammaMeasure (k : ℝ) 1).prod (gammaMeasure (l : ℝ) 1) := by
    filter_upwards [hdimK, hdimC] with a ha hb
    exact stdGaussian_orthogonal_energy_pair_law (K a) k l hk hl ha hb
  exact ((MeasurePreserving.id μ).skew_product
    (measurable_gaussianSplitEnergy K hproj) hFiber).map_eq

/-- Transfer the random-subspace law to actual independent random variables.
Independence from the fresh Gaussian vector is essential, rather than inferred
from a fixed-subspace calculation. -/
theorem indep_stdGaussian_random_split_energy_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → A) (Y : Ω → E) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P) (hGaussian : P.map Y = stdGaussian E)
    (K : A → Submodule ℝ E)
    (hproj : Measurable (fun p : A × E => (K p.1).starProjection p.2))
    (k l : ℕ) (hk : 0 < k) (hl : 0 < l)
    (hdimK : ∀ᵐ a ∂P.map X, Module.finrank ℝ (K a) = 2 * k)
    (hdimC : ∀ᵐ a ∂P.map X, Module.finrank ℝ (K a)ᗮ = 2 * l) :
    P.map (fun ω => (X ω, gaussianSplitEnergy (K (X ω)) (Y ω))) =
      (P.map X).prod ((gammaMeasure (k : ℝ) 1).prod (gammaMeasure (l : ℝ) 1)) := by
  have hPair := hXY.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable
  rw [hGaussian] at hPair
  have hLaw := stdGaussian_random_split_energy_law (P.map X) K hproj k l hk hl hdimK hdimC
  rw [← hPair, Measure.map_map
    (measurable_fst.prodMk (measurable_gaussianSplitEnergy K hproj))
    (hX.prodMk hY)] at hLaw
  exact hLaw

end
end JinWishart

#print axioms JinWishart.gaussianSplitEnergy_eq_ambient
#print axioms JinWishart.stdGaussian_orthogonal_energy_pair_law
#print axioms JinWishart.measurable_gaussianSplitEnergy
#print axioms JinWishart.stdGaussian_random_split_energy_law
#print axioms JinWishart.indep_stdGaussian_random_split_energy_law
