import JinWishartFormalization.WishartProbability
import Mathlib.Analysis.InnerProductSpace.Adjoint
import JinWishartFormalization.GaussianRadialCDF

/-!
# Actual Gaussian laws for the dimension-independent Bartlett route

An orthogonal projection onto its own subspace has the standard Gaussian law
of that subspace. This is a genuine pushforward law, not a hypothetical
residual density; residual dimension and Gamma norm law remain separate.
[需人工审查] Use with complex variance scaling and conditional random subspaces.
-/

open MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

/-- A coisometry maps the actual standard Gaussian to the actual standard Gaussian. -/
theorem stdGaussian_map_adjoint_norm_preserving (L : E →L[ℝ] F)
    (hL : ∀ t : F, ‖L.adjoint t‖ = ‖t‖) :
    (stdGaussian E).map L = stdGaussian F := by
  apply Measure.ext_of_charFun
  funext t
  have hc : charFun ((stdGaussian E).map L) t =
      charFun (stdGaussian E) (L.adjoint t) := by
    rw [charFun_apply, integral_map (by fun_prop) (by fun_prop), charFun_apply]
    simp_rw [← L.adjoint_inner_right]
  rw [hc, charFun_stdGaussian, charFun_stdGaussian, hL]

/-- The subspace-valued orthogonal projection law, in every finite dimension. -/
theorem stdGaussian_orthogonalProjectionOnto_law
    (K : Submodule ℝ E) :
    (stdGaussian E).map K.orthogonalProjectionOnto = stdGaussian K := by
  apply stdGaussian_map_adjoint_norm_preserving
  intro t
  rw [K.adjoint_orthogonalProjectionOnto]
  rfl

/-- Reuse the established radial Gamma law in an arbitrary even-dimensional space.
This changes coordinates by an isometry; it does not redo radial integration. -/
theorem stdGaussian_half_norm_sq_law (k : ℕ) (hk : 0 < k)
    (hdim : Module.finrank ℝ E = 2 * k) :
    (stdGaussian E).map (fun z : E => ‖z‖ ^ 2 / 2) = gammaMeasure (k : ℝ) 1 := by
  let b := stdOrthonormalBasis ℝ E
  have hpositive : 0 < Module.finrank ℝ E := by omega
  letI : Nonempty (Fin (Module.finrank ℝ E)) := Fin.pos_iff_nonempty.mp hpositive
  have h := stdGaussian_euclideanEnergy_map_eq_gammaMeasure
    (ι := Fin (Module.finrank ℝ E)) k (by simpa using hdim) hk
  have hc := stdGaussian_map b.repr
  rw [← hc, Measure.map_map (by fun_prop) (by fun_prop)] at h
  simpa only [Function.comp_def, euclideanGaussianEnergy, b.repr.norm_map] using h

/-- Fixed-subspace residual energy is Gamma with half the real dimension.
The subspace is deterministic: a random QR subspace still needs a conditional-law bridge. -/
theorem stdGaussian_projected_half_norm_sq_law (K : Submodule ℝ E)
    (k : ℕ) (hk : 0 < k) (hdim : Module.finrank ℝ K = 2 * k) :
    (stdGaussian E).map (fun z : E => ‖K.orthogonalProjectionOnto z‖ ^ 2 / 2) =
      gammaMeasure (k : ℝ) 1 := by
  have h := stdGaussian_half_norm_sq_law (E := K) k hk hdim
  rw [← stdGaussian_orthogonalProjectionOnto_law K,
    Measure.map_map (by fun_prop) (by fun_prop)] at h
  exact h

end
end JinWishart

#print axioms JinWishart.stdGaussian_map_adjoint_norm_preserving
#print axioms JinWishart.stdGaussian_orthogonalProjectionOnto_law
#print axioms JinWishart.stdGaussian_half_norm_sq_law
#print axioms JinWishart.stdGaussian_projected_half_norm_sq_law
