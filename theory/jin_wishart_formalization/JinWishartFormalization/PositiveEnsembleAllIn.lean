import JinWishartFormalization.PositiveDeterminantEnsembleCount
import Mathlib.Algebra.Polynomial.Eval.Coeff

/-! Codex. Seed 2026103005 exact finite ensemble controls precede source.
Generic all-coordinate event for a normalized determinant ensemble; this does
not identify any Wishart eigenvalue law. [需人工审查] Event/measure restriction. -/
open MeasureTheory Matrix Polynomial Set Finset
namespace JinWishart
noncomputable section
variable {n : ℕ} {μ : Measure ℝ} [SigmaFinite μ]

theorem coeff_zero_rowAffine_det (A B : Matrix (Fin n) (Fin n) ℝ) :
 ((rowAffinePolynomialMatrix A B).det).coeff 0 = B.det := by
 rw [Polynomial.coeff_zero_eq_eval_zero]
 change (Polynomial.evalRingHom (0 : ℝ)) (rowAffinePolynomialMatrix A B).det = B.det
 rw [RingHom.map_det]
 congr 1
 ext i j
 simp [rowAffinePolynomialMatrix]

theorem coordinateMembershipCount_compl_eq_zero_iff (E : Set ℝ) (z : Fin n → ℝ) :
 coordinateMembershipCount Eᶜ z = 0 ↔ ∀ i, z i ∈ E := by
 classical
 simp [coordinateMembershipCount,Finset.filter_eq_empty_iff]

theorem normalizedDeterminantEnsemble_allIn (f g : Fin n → ℝ → ℝ)
 (hfg : ∀ i j, Integrable (fun y => f i y*g j y) μ)
 (hpos : ∀ z, 0 ≤ determinantProduct f g z)
 (hdet : 0 < (determinantMomentMatrix μ f g).det)
 (E : Set ℝ) (hE : MeasurableSet E) :
 ((normalizedDeterminantEnsemble μ f g) {z | ∀ i, z i ∈ E}).toReal =
   (Matrix.of (fun i j => ∫ y in E, f i y*g j y ∂μ)).det /
     (determinantMomentMatrix μ f g).det := by
 have h := (normalizedDeterminantEnsemble_probability_count f g hfg hpos hdet).2 Eᶜ hE.compl 0 (Nat.zero_le _)
 have hs : {z : Fin n → ℝ | coordinateMembershipCount Eᶜ z = 0} =
     {z : Fin n → ℝ | ∀ i, z i ∈ E} := by
   ext z
   exact coordinateMembershipCount_compl_eq_zero_iff E z
 rw [hs,coeff_zero_rowAffine_det] at h
 simpa using h

end
end JinWishart
#print axioms JinWishart.coeff_zero_rowAffine_det
#print axioms JinWishart.coordinateMembershipCount_compl_eq_zero_iff
#print axioms JinWishart.normalizedDeterminantEnsemble_allIn
