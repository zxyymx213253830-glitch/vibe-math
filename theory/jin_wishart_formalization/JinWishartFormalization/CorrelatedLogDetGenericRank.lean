import JinWishartFormalization.CorrelatedGaussianGenericRank
import JinWishartFormalization.CorrelatedLogDetExpectedRank
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-! Explicit generic-rank value of the actual expected full-logdet prelog.
Fixed arbitrary B, M; includes singular/rectangular factors and all zero shapes.
Codex. [需人工审查] Inherited null-set/DCT/variance/model correspondence.
No coding theorem or uniformity for SNR-varying B/M is asserted.
-/
open Matrix Module MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace JinWishart
noncomputable section

theorem matrix_fromRows_rank_eq {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) :
    (Matrix.fromRows B M).rank = B.rank +
      finrank ℂ (LinearMap.range (M.mulVecLin.domRestrict (LinearMap.ker B.mulVecLin))) := by
  have hk : LinearMap.ker (Matrix.fromRows B M).mulVecLin =
      LinearMap.ker (B.mulVecLin.prod M.mulVecLin) := by
    ext x
    change Matrix.fromRows B M *ᵥ x=0 ↔ (B*ᵥ x,M*ᵥ x)=0
    rw [Matrix.fromRows_mulVec]
    constructor
    · intro h
      apply Prod.ext
      · exact funext (fun i => congrFun h (Sum.inl i))
      · exact funext (fun i => congrFun h (Sum.inr i))
    · intro h
      have h₁ := congrArg Prod.fst h
      have h₂ := congrArg Prod.snd h
      funext i
      cases i <;> simp_all
  have h₁ := (Matrix.fromRows B M).mulVecLin.finrank_range_add_finrank_ker
  have h₂ := (B.mulVecLin.prod M.mulVecLin).finrank_range_add_finrank_ker
  rw [hk] at h₁
  have he := linearMap_pair_rank B.mulVecLin M.mulVecLin
  change finrank ℂ (LinearMap.range (Matrix.fromRows B M).mulVecLin) = _
  change finrank ℂ (LinearMap.range (B.mulVecLin.prod M.mulVecLin)) =
    B.rank+finrank ℂ (LinearMap.range (M.mulVecLin.domRestrict (LinearMap.ker B.mulVecLin))) at he
  omega

theorem actualCorrelatedMatrixLogDet_prelog_generic_rank {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) :
    Tendsto (fun r : ℝ => (∫ z, actualCorrelatedMatrixLogDet B M r z ∂stdGaussian _)/Real.log r)
      atTop (𝓝 ((min m (B.rank+
        finrank ℂ (LinearMap.range (M.mulVecLin.domRestrict (LinearMap.ker B.mulVecLin))))) : ℝ)) := by
  have h := actualCorrelatedMatrixLogDet_prelog_expected_rank B M
  have he : (∫ z : ComplexSample (m := m) (n := p),
        ((complexSampleMatrix z*B+M).rank : ℝ) ∂stdGaussian _) =
      ((min m (B.rank+finrank ℂ (LinearMap.range
        (M.mulVecLin.domRestrict (LinearMap.ker B.mulVecLin))))) : ℝ) := by
    calc
      _ = ∫ _z : ComplexSample (m := m) (n := p),
          ((min m (B.rank+finrank ℂ (LinearMap.range
            (M.mulVecLin.domRestrict (LinearMap.ker B.mulVecLin))))) : ℝ) ∂stdGaussian _ := by
        apply integral_congr_ae
        filter_upwards [actualCorrelatedRank_eq_generic_ae B M] with z hz
        exact_mod_cast hz
      _ = _ := by simp
  rwa [he] at h

theorem actualCorrelatedMatrixLogDet_prelog_stacked_rank {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) :
    Tendsto (fun r : ℝ => (∫ z, actualCorrelatedMatrixLogDet B M r z ∂stdGaussian _)/Real.log r)
      atTop (𝓝 ((min m (Matrix.fromRows B M).rank) : ℝ)) := by
  rw [matrix_fromRows_rank_eq]
  simpa only [Nat.cast_add] using actualCorrelatedMatrixLogDet_prelog_generic_rank B M

end
end JinWishart
#print axioms JinWishart.matrix_fromRows_rank_eq
#print axioms JinWishart.actualCorrelatedMatrixLogDet_prelog_generic_rank
#print axioms JinWishart.actualCorrelatedMatrixLogDet_prelog_stacked_rank
