import JinWishartFormalization.CanonicalShearFactorMoments

/-! Same-source physical canonical Fin Gram and AE positive-coordinate bounds.
The full stacked-rank hypothesis is explicit (as after common-kernel compression).
[需人工审查] Inherited AE Gaussian rank/model; final inverse integration remains open. -/
open Matrix MeasureTheory ProbabilityTheory
open scoped ComplexOrder
namespace JinWishart
noncomputable section

def canonicalPhysicalFinSample {a b c m p n : ℕ}
    (er : (Fin a ⊕ Fin c) ≃ Fin m) (ec : (Fin b ⊕ Fin c) ≃ Fin n)
    (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin a ⊕ Fin c))
    (U : Matrix (Fin p) (Fin b) ℂ) (A : Matrix (Fin a) (Fin b) ℂ)
    (H : Matrix (Fin c) (Fin b) ℂ) (N : Matrix (Fin c) (Fin c) ℂ)
    (Z : Matrix (Fin m) (Fin p) ℂ) : Matrix (Fin m) (Fin n) ℂ :=
  canonicalFinBlock er ec
    (fun i j => V (complexMatrixColumn (Z*U) j) (Sum.inl i)+A i j)
    (fun i j => V (complexMatrixColumn (Z*U) j) (Sum.inr i)+H i j) N

private theorem rowReindexedGram {a c m n : ℕ}
    (er : (Fin a ⊕ Fin c) ≃ Fin m) (Y : Matrix (Fin a ⊕ Fin c) (Fin n) ℂ) :
    (Y.submatrix er.symm id)ᴴ*Y.submatrix er.symm id=Yᴴ*Y := by
  ext j k
  change (∑ i : Fin m, star (Y (er.symm i) j)*Y (er.symm i) k)=
    ∑ i : Fin a ⊕ Fin c, star (Y i j)*Y i k
  exact Fintype.sum_equiv er.symm _ _ (by intro i;rfl)

theorem canonical_physical_fin_gram {m p n b a c : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (T : Matrix (Fin n) (Fin b ⊕ Fin c) ℂ) (U : Matrix (Fin p) (Fin b) ℂ)
    (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin a ⊕ Fin c))
    (A : Matrix (Fin a) (Fin b) ℂ) (H : Matrix (Fin c) (Fin b) ℂ)
    (N : Matrix (Fin c) (Fin c) ℂ)
    (er : (Fin a ⊕ Fin c) ≃ Fin m) (ec : (Fin b ⊕ Fin c) ≃ Fin n)
    (hBT : B*T=fromCols U 0)
    (hMean : (fromBlocks A 0 H N).toEuclideanLin=
      V.toLinearEquiv.toLinearMap.comp (M*T).toEuclideanLin)
    (Z : Matrix (Fin m) (Fin p) ℂ) :
    let D := canonicalPhysicalFinSample er ec V U A H N Z
    Dᴴ*D=((Z*B+M)*(T.submatrix id ec.symm))ᴴ*((Z*B+M)*(T.submatrix id ec.symm)) := by
  have hp := canonical_physical_sample_block_identity B M T U V A H N hBT hMean Z
  have hpoint : canonicalSumRowAction V ((Z*B+M)*(T.submatrix id ec.symm))=
      (fromBlocks
        (fun i j => V (complexMatrixColumn (Z*U) j) (Sum.inl i)+A i j) 0
        (fun i j => V (complexMatrixColumn (Z*U) j) (Sum.inr i)+H i j) N).submatrix id ec.symm := by
    ext i j
    exact congrArg (fun W => W i (ec.symm j)) hp
  have hd : canonicalPhysicalFinSample er ec V U A H N Z=
      (canonicalSumRowAction V ((Z*B+M)*(T.submatrix id ec.symm))).submatrix er.symm id := by
    rw [hpoint]
    rfl
  dsimp only
  rw [hd,rowReindexedGram,canonicalSumRowAction_gram]

private theorem eigenvalueCongr {n : ℕ} {G J : Matrix (Fin n) (Fin n) ℂ}
    (hG : G.IsHermitian) (hJ : J.IsHermitian) (h : G=J) :
    hG.eigenvalues₀=hJ.eigenvalues₀ := by
  subst J
  rfl

theorem actual_canonical_fin_positive_bounds_ae {m p n b a c : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (T : Matrix (Fin n) (Fin b ⊕ Fin c) ℂ) (U : Matrix (Fin p) (Fin b) ℂ)
    (V : EuclideanSpace ℂ (Fin m) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin a ⊕ Fin c))
    (A : Matrix (Fin a) (Fin b) ℂ) (H : Matrix (Fin c) (Fin b) ℂ)
    (N : Matrix (Fin c) (Fin c) ℂ)
    (er : (Fin a ⊕ Fin c) ≃ Fin m) (ec : (Fin b ⊕ Fin c) ≃ Fin n)
    (hBT : B*T=fromCols U 0)
    (hMean : (fromBlocks A 0 H N).toEuclideanLin=
      V.toLinearEquiv.toLinearMap.comp (M*T).toEuclideanLin)
    (hT : Function.Bijective T.toEuclideanLin) (hstack : (Matrix.fromRows B M).rank=n)
    (hm : 0<m) (hn : 0<n) (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=min m n) :
    ∀ᵐ z ∂stdGaussian (ComplexSample (m := m) (n := p)),
      let D := canonicalPhysicalFinSample er ec V U A H N (complexSampleMatrix z)
      let F := T.submatrix id ec.symm
      0<actualCorrelatedEigenvalue B M i z ∧
      0<(complexGram_posSemidef D).1.eigenvalues₀ i ∧
      (complexGram_posSemidef D).1.eigenvalues₀ i≤
        max (matrixColumnControl F) (matrixColumnControl Fᴴ)*actualCorrelatedEigenvalue B M i z ∧
      actualCorrelatedEigenvalue B M i z≤
        max (matrixColumnControl F⁻¹) (matrixColumnControl (Fᴴ)⁻¹)*
          (complexGram_posSemidef D).1.eigenvalues₀ i := by
  filter_upwards [actualCorrelatedRank_eq_generic_ae B M] with z hz
  rw [← matrix_fromRows_rank_eq B M,hstack] at hz
  let X := complexSampleMatrix z*B+M
  let F := T.submatrix id ec.symm
  let D := canonicalPhysicalFinSample er ec V U A H N (complexSampleMatrix z)
  have hc := canonical_fin_positive_coordinate_bounds V X T hT ec hm hn hz i hi
  have hG : Dᴴ*D=
      (canonicalSumRowAction V (X*F))ᴴ*canonicalSumRowAction V (X*F) :=
    (canonical_physical_fin_gram B M T U V A H N er ec hBT hMean (complexSampleMatrix z)).trans
      (canonicalSumRowAction_gram V (X*F)).symm
  have heq : canonicalFiniteGramCoordinate V X T ec i=(complexGram_posSemidef D).1.eigenvalues₀ i :=
    (congrFun (eigenvalueCongr (complexGram_posSemidef D).1
      (Matrix.isHermitian_conjTranspose_mul_self (canonicalSumRowAction V (X*F))) hG) i).symm
  dsimp only at hc
  rw [heq] at hc
  exact hc

end
end JinWishart
#print axioms JinWishart.canonical_physical_fin_gram
#print axioms JinWishart.actual_canonical_fin_positive_bounds_ae
