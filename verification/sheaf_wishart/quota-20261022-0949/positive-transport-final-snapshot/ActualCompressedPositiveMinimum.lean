import JinWishartFormalization.GramPositiveSpectrumTransport
import JinWishartFormalization.CorrelatedFixedKernelCompression

/-! A fixed kernel compression preserves the actual AE smallest positive Gram
coordinate on the SAME original Gaussian source. Codex.
[需人工审查] AE spectral/model correspondence. No whitening or inverse threshold. -/
open Matrix MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

theorem exists_actual_fixed_compression_min_positive_ae {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (hR : 0<min m (Matrix.fromRows B M).rank) :
    ∃ (r : ℕ) (C : Matrix (Fin n) (Fin r) ℂ),
      r=(Matrix.fromRows B M).rank ∧ Cᴴ*C=1 ∧ B*C*Cᴴ=B ∧ M*C*Cᴴ=M ∧
      ∃ (i : Fin (Fintype.card (Fin n))) (j : Fin (Fintype.card (Fin r))),
        i.val+1=min m (Matrix.fromRows B M).rank ∧
        j.val+1=min m (Matrix.fromRows B M).rank ∧
        Measurable (actualCorrelatedEigenvalue B M i) ∧
        Measurable (actualCorrelatedEigenvalue (B*C) (M*C) j) ∧
        ∀ᵐ z ∂stdGaussian (ComplexSample (m := m) (n := p)),
          0<actualCorrelatedEigenvalue B M i z ∧
          0<actualCorrelatedEigenvalue (B*C) (M*C) j z ∧
          actualCorrelatedEigenvalue B M i z=actualCorrelatedEigenvalue (B*C) (M*C) j z := by
  obtain ⟨r,C,hr,hiso,hB,hM,hZ⟩ := exists_correlated_fixed_kernel_compression B M
  have hstack : Matrix.fromRows (B*C) (M*C)=Matrix.fromRows B M*C :=
    (Matrix.fromRows_mul B M C).symm
  have hrecover : Matrix.fromRows B M*C*Cᴴ=Matrix.fromRows B M := by
    rw [Matrix.fromRows_mul,Matrix.fromRows_mul,hB,hM]
  have hRank : (Matrix.fromRows (B*C) (M*C)).rank=(Matrix.fromRows B M).rank := by
    rw [hstack]
    apply le_antisymm (Matrix.rank_mul_le_left _ _)
    have h := Matrix.rank_mul_le_left (Matrix.fromRows B M*C) Cᴴ
    rwa [hrecover] at h
  have hRc : 0<min m (Matrix.fromRows (B*C) (M*C)).rank := by rw [hRank];exact hR
  obtain ⟨i,hi,hmi,hxi⟩ := exists_actualCorrelated_smallest_positive_coordinate B M hR
  obtain ⟨j,hj,hmj,hyj⟩ := exists_actualCorrelated_smallest_positive_coordinate (B*C) (M*C) hRc
  refine ⟨r,C,hr,hiso,hB,hM,i,j,hi,?_,hmi,hmj,?_⟩
  · simpa only [hRank] using hj
  · filter_upwards [hxi,hyj] with z hx hy
    have hs : complexSampleMatrix z*(B*C)+M*C=(complexSampleMatrix z*B+M)*C := by
      rw [Matrix.add_mul,Matrix.mul_assoc]
    have hrow : (complexSampleMatrix z*B+M)*(complexSampleMatrix z*B+M)ᴴ=
        (complexSampleMatrix z*(B*C)+M*C)*(complexSampleMatrix z*(B*C)+M*C)ᴴ := by
      rw [hs]
      exact (hZ (complexSampleMatrix z)).2.symm
    exact ⟨hx.1,hy.1,gram_min_positive_eq_of_rowGram_eq _ _ hrow
      i j hx.1 hy.1 hx.2 hy.2⟩

end
end JinWishart
#print axioms JinWishart.exists_actual_fixed_compression_min_positive_ae
