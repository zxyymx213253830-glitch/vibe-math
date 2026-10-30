import JinWishartFormalization.PositiveEnsembleAllIn
import JinWishartFormalization.MixedEnsembleProbability

/-! Codex. Seed 2026103005:40 exact finite ensemble controls precede source.
All-in, upper-tail and lower-cutoff events for the formula-side candidate.
No actual Wishart spectrum law or identification with Psi/Xi is claimed.
[需人工审查] Set restrictions, Fubini and later physical model mapping. -/
open MeasureTheory Matrix Set
namespace JinWishart
noncomputable section

theorem mixedCandidateEnsemble_allIn (p L q : ℕ) (lambda : Fin L → ℝ)
 (hl : StrictMono lambda) (hlp : ∀ j, 0 < lambda j) (E : Set ℝ) (hE : MeasurableSet E) :
 ((mixedCandidateEnsemble p L q lambda) {z | ∀ i, z i ∈ E}).toReal =
 (Matrix.of (fun i j => ∫ y in E, mixedEnsembleF p L i y * mixedEnsembleG p L q lambda j y
   ∂(volume.restrict (Ioi (0 : ℝ))))).det /
 (determinantMomentMatrix (volume.restrict (Ioi (0 : ℝ)))
   (mixedEnsembleF p L) (mixedEnsembleG p L q lambda)).det := by
 unfold mixedCandidateEnsemble
 exact normalizedDeterminantEnsemble_allIn
   (mixedEnsembleF p L) (mixedEnsembleG p L q lambda)
   (fun i j => (mixedEnsemble_pair_moment p L q lambda (fun a => (hlp a).le) i j).1)
   (mixedDeterminantProduct_nonneg p L q lambda hl hlp)
   (mixedEnsemble_momentMatrix_det_pos p L q lambda hl hlp) E hE

theorem mixedCandidateEnsemble_all_le (p L q : ℕ) (lambda : Fin L → ℝ)
 (hl : StrictMono lambda) (hlp : ∀ j, 0 < lambda j) (t : ℝ) :
 ((mixedCandidateEnsemble p L q lambda) {z | ∀ i, z i ≤ t}).toReal =
 (Matrix.of (fun i j => ∫ y in Iic t, mixedEnsembleF p L i y * mixedEnsembleG p L q lambda j y
   ∂(volume.restrict (Ioi (0 : ℝ))))).det /
 (determinantMomentMatrix (volume.restrict (Ioi (0 : ℝ)))
   (mixedEnsembleF p L) (mixedEnsembleG p L q lambda)).det := by
 exact mixedCandidateEnsemble_allIn p L q lambda hl hlp (Iic t) measurableSet_Iic

theorem mixedCandidateEnsemble_all_gt (p L q : ℕ) (lambda : Fin L → ℝ)
 (hl : StrictMono lambda) (hlp : ∀ j, 0 < lambda j) (t : ℝ) :
 ((mixedCandidateEnsemble p L q lambda) {z | ∀ i, t < z i}).toReal =
 (Matrix.of (fun i j => ∫ y in Ioi t, mixedEnsembleF p L i y * mixedEnsembleG p L q lambda j y
   ∂(volume.restrict (Ioi (0 : ℝ))))).det /
 (determinantMomentMatrix (volume.restrict (Ioi (0 : ℝ)))
   (mixedEnsembleF p L) (mixedEnsembleG p L q lambda)).det := by
 exact mixedCandidateEnsemble_allIn p L q lambda hl hlp (Ioi t) measurableSet_Ioi

end
end JinWishart
#print axioms JinWishart.mixedCandidateEnsemble_allIn
#print axioms JinWishart.mixedCandidateEnsemble_all_le
#print axioms JinWishart.mixedCandidateEnsemble_all_gt
