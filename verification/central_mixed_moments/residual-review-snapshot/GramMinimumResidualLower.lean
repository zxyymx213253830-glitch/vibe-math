import JinWishartFormalization.GramMinimumRayleigh

/-!
# The least Gram eigenvalue is no larger than any leave-one-out residual

Codex deterministic proof; no full-rank or generic-position assumption.
The test vector has distinguished coordinate1, hence norm at least1.
[需人工审查] Later correspondence to actual Gaussian residual events.
-/
open Matrix
open scoped BigOperators ComplexOrder
namespace JinWishart
noncomputable section

theorem exists_leaveOneOut_residual_test_vector {m n : ℕ}
    (A : Matrix (Fin m) (Fin (n+1)) ℂ) (j : Fin (n+1)) :
    ∃ u : EuclideanSpace ℂ (Fin (n+1)), u j=1 ∧
      A.toEuclideanLin u = (leaveOneOutColumnSpace A j)ᗮ.starProjection (complexMatrixColumn A j) := by
  classical
  let K := leaveOneOutColumnSpace A j
  obtain ⟨c,hc⟩ := K.starProjection_apply_mem (complexMatrixColumn A j)
  let u : EuclideanSpace ℂ (Fin (n+1)) := WithLp.toLp 2 (j.insertNth 1 (fun i => -c i))
  refine ⟨u,?_,?_⟩
  · simp [u]
  · rw [matrix_column_sum,Fin.sum_univ_succAbove _ j]
    simp only [u,PiLp.toLp_apply,Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove]
    simp only [one_smul,neg_smul]
    have hsum : (∑ i : Fin n, c i • complexMatrixColumn A (j.succAbove i)) =
        (A.submatrix id j.succAbove).toEuclideanLin c := by
      rw [matrix_column_sum]
      rfl
    rw [Finset.sum_neg_distrib,hsum,hc]
    have h := K.starProjection_add_starProjection_orthogonal (complexMatrixColumn A j)
    exact eq_sub_of_add_eq' h |>.symm

theorem gramSmallestValue_le_leaveOneOut_energy {m n : ℕ}
    (A : Matrix (Fin m) (Fin (n+1)) ℂ) (j : Fin (n+1)) :
    gramSmallestValue A (Nat.succ_pos n) ≤ leaveOneOutResidualEnergy A j := by
  obtain ⟨u,huj,hu⟩ := exists_leaveOneOut_residual_test_vector A j
  have hnrm : 1 ≤ ‖u‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    have h := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => sq_nonneg ‖u i‖)
      (Finset.mem_univ j)
    simpa only [huj,norm_one,one_pow] using h
  have h := gramSmallestValue_rayleigh_lower A (Nat.succ_pos n) u
  rw [hu] at h
  change gramSmallestValue A (Nat.succ_pos n)*‖u‖^2 ≤ leaveOneOutResidualEnergy A j at h
  have hmin : 0 ≤ gramSmallestValue A (Nat.succ_pos n) :=
    complexGram_eigenvalues₀_nonneg A (smallestEigenvalue₀Index (Nat.succ_pos n))
  nlinarith

end
end JinWishart
#print axioms JinWishart.exists_leaveOneOut_residual_test_vector
#print axioms JinWishart.gramSmallestValue_le_leaveOneOut_energy
