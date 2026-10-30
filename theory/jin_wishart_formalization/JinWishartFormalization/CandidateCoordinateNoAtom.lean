import JinWishartFormalization.CandidatePaperExtremeCDF

/-! Codex. Seed 2026103103 continuous-coordinate and atomic negative controls
precede source. Candidate coordinate no-atoms only, not actual spectrum law.
[需人工审查] Product measure and AE transfer. -/
open MeasureTheory Set
namespace JinWishart
noncomputable section

theorem mixedCandidateEnsemble_coordinate_noAtom (p L q : ℕ) (lambda : Fin L → ℝ)
 (i : Fin (p+L)) (x : ℝ) :
 mixedCandidateEnsemble p L q lambda {z | z i = x} = 0 := by
 let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
 have hac : mixedCandidateEnsemble p L q lambda ≪ Measure.pi (fun _ : Fin (p+L) => μ) := by
   unfold mixedCandidateEnsemble normalizedDeterminantEnsemble determinantEnsembleMeasure
   exact Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)
 apply hac
 exact Measure.pi_hyperplane (fun _ : Fin (p+L) => μ) i x

theorem mixedCandidateEnsemble_coordinates_ne_ae (p L q : ℕ) (lambda : Fin L → ℝ) (x : ℝ) :
 ∀ᵐ z ∂mixedCandidateEnsemble p L q lambda, ∀ i, z i ≠ x := by
 apply Filter.eventually_all.2
 intro i
 apply compl_mem_ae_iff.2
 change mixedCandidateEnsemble p L q lambda {z | z i = x} = 0
 exact mixedCandidateEnsemble_coordinate_noAtom p L q lambda i x

theorem mixedCandidateEnsemble_all_le_eq_all_lt (p L q : ℕ) (lambda : Fin L → ℝ) (x : ℝ) :
 mixedCandidateEnsemble p L q lambda {z | ∀ i, z i ≤ x} =
 mixedCandidateEnsemble p L q lambda {z | ∀ i, z i < x} := by
 apply measure_congr
 filter_upwards [mixedCandidateEnsemble_coordinates_ne_ae p L q lambda x] with z hz
 apply propext
 constructor
 · intro h i
   exact lt_of_le_of_ne (h i) (hz i)
 · intro h i
   exact (h i).le

theorem mixedCandidateEnsemble_exists_le_eq_exists_lt (p L q : ℕ) (lambda : Fin L → ℝ) (x : ℝ) :
 mixedCandidateEnsemble p L q lambda {z | ∃ i, z i ≤ x} =
 mixedCandidateEnsemble p L q lambda {z | ∃ i, z i < x} := by
 apply measure_congr
 filter_upwards [mixedCandidateEnsemble_coordinates_ne_ae p L q lambda x] with z hz
 apply propext
 constructor
 · rintro ⟨i,hi⟩
   exact ⟨i,lt_of_le_of_ne hi (hz i)⟩
 · rintro ⟨i,hi⟩
   exact ⟨i,hi.le⟩

theorem mixedCandidateEnsemble_all_ge_eq_all_gt (p L q : ℕ) (lambda : Fin L → ℝ) (x : ℝ) :
 mixedCandidateEnsemble p L q lambda {z | ∀ i, x ≤ z i} =
 mixedCandidateEnsemble p L q lambda {z | ∀ i, x < z i} := by
 apply measure_congr
 filter_upwards [mixedCandidateEnsemble_coordinates_ne_ae p L q lambda x] with z hz
 apply propext
 constructor
 · intro h i
   exact lt_of_le_of_ne (h i) (Ne.symm (hz i))
 · intro h i
   exact (h i).le

theorem mixedCandidateEnsemble_exists_ge_eq_exists_gt (p L q : ℕ) (lambda : Fin L → ℝ) (x : ℝ) :
 mixedCandidateEnsemble p L q lambda {z | ∃ i, x ≤ z i} =
 mixedCandidateEnsemble p L q lambda {z | ∃ i, x < z i} := by
 apply measure_congr
 filter_upwards [mixedCandidateEnsemble_coordinates_ne_ae p L q lambda x] with z hz
 apply propext
 constructor
 · rintro ⟨i,hi⟩
   exact ⟨i,lt_of_le_of_ne hi (Ne.symm (hz i))⟩
 · rintro ⟨i,hi⟩
   exact ⟨i,hi.le⟩

end
end JinWishart
#print axioms JinWishart.mixedCandidateEnsemble_coordinate_noAtom
#print axioms JinWishart.mixedCandidateEnsemble_coordinates_ne_ae
#print axioms JinWishart.mixedCandidateEnsemble_all_le_eq_all_lt
#print axioms JinWishart.mixedCandidateEnsemble_exists_le_eq_exists_lt
#print axioms JinWishart.mixedCandidateEnsemble_all_ge_eq_all_gt
#print axioms JinWishart.mixedCandidateEnsemble_exists_ge_eq_exists_gt
