import JinWishartFormalization.ActualCompressedInverseCriterion
import JinWishartFormalization.CorrelatedNoiselessInverseMoments
import JinWishartFormalization.CorrelatedMinimumZeroAtom

/-! Two fixed-source inverse-moment edge branches. Codex.
Controls seed2026102237:27 exact cases/198 checks, fixed right inverse and
scalar |z|^2+1 reference. [需人工审查] Boundary/row correspondence and integral
domination inherited from the noiseless floor theorem. The zero-noise result
concerns totalized real inverse powers, including constant zero coordinates;
it does not invent a minimum-positive coordinate when generic rank is zero. -/
open Matrix Module MeasureTheory ProbabilityTheory
open scoped ComplexOrder
namespace JinWishart
noncomputable section

theorem actual_inverse_realMoment_integrable_of_noise_rank_zero {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (hB : B.rank=0) (i : Fin (Fintype.card (Fin n))) (q : ℝ) :
    Integrable (fun z => (actualCorrelatedEigenvalue B M i z)⁻¹^q)
      (stdGaussian (ComplexSample (m := m) (n := p))) := by
  have hL : B.mulVecLin=0 :=
    LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hB)
  change B.toLin'=0 at hL
  have hbz : B=0 := by
    have hh := congrArg LinearMap.toMatrix' hL
    simpa only [LinearMap.toMatrix'_toLin',map_zero] using hh
  subst B
  simpa only [actualCorrelatedEigenvalue,Matrix.mul_zero,zero_add] using
    (integrable_const (((complexGram_posSemidef M).1.eigenvalues₀ i)⁻¹^q) :
      Integrable (fun _ : ComplexSample (m := m) (n := p) =>
        ((complexGram_posSemidef M).1.eigenvalues₀ i)⁻¹^q) (stdGaussian _))

theorem actual_positive_boundary_inverse_integrable_of_noiseless_full_image {m p n r : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (hr : r=(Matrix.fromRows B M).rank) (hm : 0<m) (hc : r-B.rank=m)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=min m r)
    (q : ℝ) (hq : 0≤q) :
    Integrable (fun z => (actualCorrelatedEigenvalue B M i z)⁻¹^q)
      (stdGaussian (ComplexSample (m := m) (n := p))) := by
  have hd := matrix_fromRows_rank_eq B M
  rw [← hr] at hd
  have hs : finrank ℂ (LinearMap.range
      (M.mulVecLin.domRestrict (LinearMap.ker B.mulVecLin)))=m := by omega
  have him : i.val+1=m := by omega
  obtain ⟨δ,hδ,hfloor⟩ := correlated_rowGram_uniform_floor B M hm hs
  have heq : (fun z => (actualCorrelatedEigenvalue B M i z)⁻¹^q)=ᵐ[
      stdGaussian (ComplexSample (m := m) (n := p))]
      (fun z => (gramSmallestValue (complexSampleMatrix z*B+M)ᴴ hm)⁻¹^q) := by
    apply ae_of_all
    intro z
    have hp : 0<gramSmallestValue (complexSampleMatrix z*B+M)ᴴ hm :=
      hδ.trans_le (hfloor (complexSampleMatrix z))
    have hRank : (complexSampleMatrix z*B+M).rank=m := by
      have hh := (gramSmallestValue_pos_iff_rank _ hm).mp hp
      rwa [Matrix.rank_conjTranspose] at hh
    have hh := (gram_full_row_rank_coordinate_eq_rowMinimum _ hm i him hRank).2
    exact congrArg (fun t : ℝ => t⁻¹^q) hh
  exact (integrable_congr heq).mpr
    (actualCorrelatedRow_inverseMoment_integrable_of_noiseless_surjective B M hm hs q hq)

end
end JinWishart
#print axioms JinWishart.actual_inverse_realMoment_integrable_of_noise_rank_zero
#print axioms JinWishart.actual_positive_boundary_inverse_integrable_of_noiseless_full_image
