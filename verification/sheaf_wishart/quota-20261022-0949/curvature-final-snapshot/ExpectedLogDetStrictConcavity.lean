import JinWishartFormalization.ExpectedLogDetCurvature
import JinWishartFormalization.CorrelatedLogDetGenericRank

/-! Strict concavity is controlled exactly by the fixed model's generic rank.
Codex. [需人工审查] Inherited AE rank, positive integration and model conventions.
All finite shapes, arbitrary fixed complex B,M; no fullrank or inverse moments. -/
open Matrix MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace JinWishart
noncomputable section

theorem gram_resolvent_square_sum_pos {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℂ)
    (r : ℝ) (hr : 0<r) (hX : 0<X.rank) :
    0<∑ i,((complexGram_posSemidef X).1.eigenvalues₀ i /
      (1+r*(complexGram_posSemidef X).1.eigenvalues₀ i))^2 := by
  classical
  have hc : 0<∑ i, if 0<(complexGram_posSemidef X).1.eigenvalues₀ i then (1:ℝ) else 0 := by
    rw [gram_positive_modes_eq_rank]
    exact_mod_cast hX
  obtain ⟨i,hi,hpos⟩ := (Finset.sum_pos_iff_of_nonneg (fun j _ => by positivity)).mp hc
  have hp : 0<(complexGram_posSemidef X).1.eigenvalues₀ i := by
    by_contra h
    simp [h] at hpos
  apply (Finset.sum_pos_iff_of_nonneg (fun j _ => sq_nonneg _)).2
  exact ⟨i,hi,sq_pos_of_pos (div_pos hp (by positivity))⟩

theorem gram_eigenvalues_zero_of_rank_zero {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℂ)
    (hX : X.rank=0) (i : Fin (Fintype.card (Fin n))) :
    (complexGram_posSemidef X).1.eigenvalues₀ i=0 := by
  classical
  have hc : (∑ j,if 0<(complexGram_posSemidef X).1.eigenvalues₀ j then (1:ℝ) else 0)=0 := by
    rw [gram_positive_modes_eq_rank,hX,Nat.cast_zero]
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => by positivity)).mp hc i (Finset.mem_univ i)
  by_contra h
  have hp : 0<(complexGram_posSemidef X).1.eigenvalues₀ i :=
    lt_of_le_of_ne (complexGram_eigenvalues₀_nonneg X i) (Ne.symm h)
  simp [hp] at hi

theorem actualCorrelated_expected_curvature_pos {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (hR : 0<min m (Matrix.fromRows B M).rank) (r : ℝ) (hr : 0<r) :
    0<∑ i,∫ z,(actualCorrelatedEigenvalue B M i z/(1+r*actualCorrelatedEigenvalue B M i z))^2 ∂stdGaussian _ := by
  classical
  let K := fun z : ComplexSample (m := m) (n := p) =>
    ∑ i,(actualCorrelatedEigenvalue B M i z/(1+r*actualCorrelatedEigenvalue B M i z))^2
  have hi (i : Fin (Fintype.card (Fin n))) :=
    (integral_resolvent_hasDerivAt (stdGaussian _) (actualCorrelatedEigenvalue B M i)
      (measurable_actualCorrelatedEigenvalue B M i) (integrable_actualCorrelatedEigenvalue B M i)
      (ae_of_all _ (actualCorrelatedEigenvalue_nonneg B M i)) r hr).1
  have hK : Integrable K (stdGaussian _) := integrable_finsetSum Finset.univ (fun i _ => hi i)
  have hKn : ∀ z,0≤K z := fun z => Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hKp : ∀ᵐ z ∂stdGaussian _,0<K z := by
    rw [matrix_fromRows_rank_eq] at hR
    filter_upwards [actualCorrelatedRank_eq_generic_ae B M] with z hz
    apply gram_resolvent_square_sum_pos (complexSampleMatrix z*B+M) r hr
    omega
  have hpos : 0<∫ z,K z ∂stdGaussian _ := by
    have hne : (∫ z,K z ∂stdGaussian _)≠0 := by
      intro hz
      have hae := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ hKn) hK).mp hz
      obtain ⟨z,hpz,hzz⟩ := (hKp.and hae).exists
      change K z=(0:ℝ) at hzz
      linarith
    exact lt_of_le_of_ne (integral_nonneg hKn) (Ne.symm hne)
  simpa only [K,integral_finsetSum _ (fun i _ => hi i)] using hpos

theorem actualCorrelated_expected_logdet_second_deriv_nonpos {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (r : ℝ) (hr : 0<r) :
    (deriv^[2] (fun x : ℝ => ∫ z,actualCorrelatedMatrixLogDet B M x z ∂stdGaussian _)) r ≤ 0 := by
  rw [actualCorrelated_expected_logdet_second_deriv B M r hr]
  exact neg_nonpos.mpr (Finset.sum_nonneg (fun i _ => integral_nonneg (fun z => sq_nonneg _)))

theorem actualCorrelated_expected_logdet_concave {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) :
    ConcaveOn ℝ (Ioi 0) (fun x : ℝ => ∫ z,actualCorrelatedMatrixLogDet B M x z ∂stdGaussian _) := by
  apply concaveOn_of_deriv2_nonpos' (convex_Ioi 0)
  · intro r hr
    exact (actualCorrelated_expected_logdet_hasDerivAt B M r hr).differentiableAt.differentiableWithinAt
  · intro r hr
    exact (actualCorrelated_expected_logdet_deriv_hasDerivAt B M r hr).differentiableAt.differentiableWithinAt
  · exact fun r hr => actualCorrelated_expected_logdet_second_deriv_nonpos B M r hr

theorem actualCorrelated_expected_logdet_strictConcave {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (hR : 0<min m (Matrix.fromRows B M).rank) :
    StrictConcaveOn ℝ (Ioi 0) (fun x : ℝ => ∫ z,actualCorrelatedMatrixLogDet B M x z ∂stdGaussian _) := by
  apply strictConcaveOn_of_deriv2_neg' (convex_Ioi 0)
  · intro r hr
    exact (actualCorrelated_expected_logdet_hasDerivAt B M r hr).continuousAt.continuousWithinAt
  · intro r hr
    rw [actualCorrelated_expected_logdet_second_deriv B M r hr]
    exact neg_lt_zero.mpr (actualCorrelated_expected_curvature_pos B M hR r hr)

theorem actualCorrelated_expected_logdet_zero_of_generic_rank_zero {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (hR : min m (Matrix.fromRows B M).rank=0) (r : ℝ) (hr : 0≤r) :
    (∫ z,actualCorrelatedMatrixLogDet B M r z ∂stdGaussian _)=0 := by
  classical
  calc
    _ = ∫ _z : ComplexSample (m := m) (n := p),(0:ℝ) ∂stdGaussian _ := by
      apply integral_congr_ae
      rw [matrix_fromRows_rank_eq] at hR
      filter_upwards [actualCorrelatedRank_eq_generic_ae B M] with z hz
      have hX : (complexSampleMatrix z*B+M).rank=0 := by omega
      rw [actualCorrelatedMatrixLogDet_eq_spectral B M r hr z]
      have he (i : Fin (Fintype.card (Fin n))) : actualCorrelatedEigenvalue B M i z=0 :=
        gram_eigenvalues_zero_of_rank_zero _ hX i
      simp [finiteSpectrumLogDet,he]
    _ = _ := by simp

theorem actualCorrelated_expected_logdet_strictConcave_iff {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ) :
    StrictConcaveOn ℝ (Ioi 0) (fun x : ℝ => ∫ z,actualCorrelatedMatrixLogDet B M x z ∂stdGaussian _) ↔
      0<min m (Matrix.fromRows B M).rank := by
  constructor
  · intro hs
    by_contra h
    have hR : min m (Matrix.fromRows B M).rank=0 := Nat.eq_zero_of_not_pos h
    have h1 := actualCorrelated_expected_logdet_zero_of_generic_rank_zero B M hR 1 (by norm_num)
    have h2 := actualCorrelated_expected_logdet_zero_of_generic_rank_zero B M hR 2 (by norm_num)
    have h3 := actualCorrelated_expected_logdet_zero_of_generic_rank_zero B M hR (3/2) (by norm_num)
    have hs' := hs.2
    have hh := hs' (x := 1) (by norm_num) (y := 2) (by norm_num) (by norm_num)
      (a := (1/2:ℝ)) (b := (1/2:ℝ)) (by norm_num) (by norm_num) (by norm_num)
    norm_num [smul_eq_mul,h1,h2,h3] at hh
  · exact actualCorrelated_expected_logdet_strictConcave B M

end
end JinWishart
#print axioms JinWishart.gram_resolvent_square_sum_pos
#print axioms JinWishart.gram_eigenvalues_zero_of_rank_zero
#print axioms JinWishart.actualCorrelated_expected_curvature_pos
#print axioms JinWishart.actualCorrelated_expected_logdet_second_deriv_nonpos
#print axioms JinWishart.actualCorrelated_expected_logdet_concave
#print axioms JinWishart.actualCorrelated_expected_logdet_strictConcave
#print axioms JinWishart.actualCorrelated_expected_logdet_zero_of_generic_rank_zero
#print axioms JinWishart.actualCorrelated_expected_logdet_strictConcave_iff
