import JinWishartFormalization.PsiCandidateLargestCDF
import JinWishartFormalization.NonnegativeScalarLaplaceUniqueness

/-! Codex. Seeds 2026103010 and 2026103102 independent Psi tail/lower controls
precede source. Original T1/T2 formula candidates match events under the
constructed candidate measure; not an actual Wishart joint-law proof.
[需人工审查] Complement event, index and paper/model correspondence. -/
open MeasureTheory Matrix Set
namespace JinWishart
noncomputable section

theorem theorem2Candidate_eq_mixedCandidate_all_le (p L q : ℕ) (lambda : Fin L → ℝ)
 (hl : StrictMono lambda) (hlp : ∀ j, 0 < lambda j) (x : ℝ) (hx : 0 ≤ x) :
 theorem2CdfCandidate (p+L) (p+L+q) L (by omega) (by omega) lambda x =
 ((mixedCandidateEnsemble p L q lambda) {z | ∀ i, z i ≤ x}).toReal := by
 rw [theorem2CdfCandidate,
   eq_sub_of_add_eq (theorem2XiMatrix_add_theorem1PsiMatrix
     (p+L) (p+L+q) L (by omega) (by omega) lambda x)]
 exact (mixedCandidateEnsemble_all_le_eq_paperPsi_ratio p L q lambda hl hlp x hx).symm

theorem theorem1Candidate_eq_mixedCandidate_exists_le (p L q : ℕ) (lambda : Fin L → ℝ)
 (hl : StrictMono lambda) (hlp : ∀ j, 0 < lambda j) (x : ℝ) (hx : 0 ≤ x) :
 theorem1CdfCandidate (p+L) (p+L+q) L (by omega) (by omega) lambda x =
 ((mixedCandidateEnsemble p L q lambda) {z | ∃ i, z i ≤ x}).toReal := by
 let μ := mixedCandidateEnsemble p L q lambda
 let A : Set (Fin (p+L) → ℝ) := {z | ∀ i, x < z i}
 letI : IsProbabilityMeasure μ := mixedCandidateEnsemble_probability p L q lambda hl hlp
 have hA : MeasurableSet A := by
   dsimp [A]
   have h := MeasurableSet.iInter (fun (i : Fin (p+L)) =>
     measurableSet_lt (measurable_const : Measurable (fun _ : Fin (p+L) → ℝ => x))
       (measurable_pi_apply i))
   convert h using 1
   ext z
   simp
 have hcompl : {z : Fin (p+L) → ℝ | ∃ i, z i ≤ x} = Aᶜ := by
   ext z
   simp [A,not_forall,not_lt]
 have hc : (μ Aᶜ).toReal = 1-(μ A).toReal := by
   have h := measureReal_compl (μ := μ) hA
   simpa [Measure.real,measureReal_def] using h
 rw [hcompl,hc,theorem1CdfCandidate]
 congr 1
 exact (mixedCandidateEnsemble_all_gt_eq_paperPsi_ratio p L q lambda hl hlp x hx).symm

end
end JinWishart
#print axioms JinWishart.theorem2Candidate_eq_mixedCandidate_all_le
#print axioms JinWishart.theorem1Candidate_eq_mixedCandidate_exists_le
