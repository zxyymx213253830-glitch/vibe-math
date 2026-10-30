import JinWishartFormalization.MixedEnsembleMoments

/-! Codex. Seeds 2026103002/3004 sign and scalar-matrix controls precede
source. Constructs a normalized formula-side measure and gives count ratios;
no equality to the actual noncentral Wishart law is asserted.
[需人工审查] Measure normalization, Fubini, indexing and model mapping. -/
open MeasureTheory Matrix Set
open scoped ENNReal
namespace JinWishart
noncomputable section

def mixedCandidateEnsemble (p L q : ℕ) (lambda : Fin L → ℝ) :
 Measure (Fin (p+L) → ℝ) :=
 normalizedDeterminantEnsemble (volume.restrict (Ioi (0 : ℝ)))
   (mixedEnsembleF p L) (mixedEnsembleG p L q lambda)

theorem mixedCandidateEnsemble_probability (p L q : ℕ) (lambda : Fin L → ℝ)
 (hl : StrictMono lambda) (hlp : ∀ j, 0 < lambda j) :
 IsProbabilityMeasure (mixedCandidateEnsemble p L q lambda) := by
 unfold mixedCandidateEnsemble
 exact (normalizedDeterminantEnsemble_probability_count
   (mixedEnsembleF p L) (mixedEnsembleG p L q lambda)
   (fun i j => (mixedEnsemble_pair_moment p L q lambda (fun a => (hlp a).le) i j).1)
   (mixedDeterminantProduct_nonneg p L q lambda hl hlp)
   (mixedEnsemble_momentMatrix_det_pos p L q lambda hl hlp)).1

theorem mixedCandidateEnsemble_count (p L q : ℕ) (lambda : Fin L → ℝ)
 (hl : StrictMono lambda) (hlp : ∀ j, 0 < lambda j)
 (E : Set ℝ) (hE : MeasurableSet E) (k : ℕ) (hk : k ≤ p+L) :
 ((mixedCandidateEnsemble p L q lambda) {z | coordinateMembershipCount E z = k}).toReal =
 ((rowAffinePolynomialMatrix
   (Matrix.of (fun i j => ∫ y in E, mixedEnsembleF p L i y * mixedEnsembleG p L q lambda j y
     ∂(volume.restrict (Ioi (0 : ℝ)))))
   (Matrix.of (fun i j => ∫ y in Eᶜ, mixedEnsembleF p L i y * mixedEnsembleG p L q lambda j y
     ∂(volume.restrict (Ioi (0 : ℝ)))))).det).coeff k /
       (determinantMomentMatrix (volume.restrict (Ioi (0 : ℝ)))
         (mixedEnsembleF p L) (mixedEnsembleG p L q lambda)).det := by
 unfold mixedCandidateEnsemble
 exact (normalizedDeterminantEnsemble_probability_count
   (mixedEnsembleF p L) (mixedEnsembleG p L q lambda)
   (fun i j => (mixedEnsemble_pair_moment p L q lambda (fun a => (hlp a).le) i j).1)
   (mixedDeterminantProduct_nonneg p L q lambda hl hlp)
   (mixedEnsemble_momentMatrix_det_pos p L q lambda hl hlp)).2 E hE k hk

end
end JinWishart
#print axioms JinWishart.mixedCandidateEnsemble_probability
#print axioms JinWishart.mixedCandidateEnsemble_count
