import JinWishartFormalization.GaussianWeightedSquareMGF
import JinWishartFormalization.GaussianMatrixPolynomialLaw
import JinWishartFormalization.WishartProbability

/-! Codex. Seed2026102507 actual properCN1 diagonal/dense controls precede source.
Only deterministic diagonal weights v_j<1 are proved here; no eigenvalue
independence or general non-diagonal transform is claimed.
[需人工审查] Product pushforward/Fubini and variance convention. -/
open Matrix MeasureTheory ProbabilityTheory Real Finset
namespace JinWishart
noncomputable section

private theorem sample_gram_diagonal (m n : ℕ) (z : ComplexSample (m := m) (n := n)) (j : Fin n) :
    (complexGram (complexSampleMatrix z) j j).re =
      ∑ i : Fin m,(z ((i,j),0)^2+z ((i,j),1)^2)/2 := by
  have hq : (Real.sqrt (2 : ℝ) : ℂ)^2=2 := by exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ)≤2))
  have hn : (Real.sqrt (2 : ℝ) : ℂ)≠0 := by exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ)<2))
  have he (i : Fin m) : star (complexSampleMatrix z i j)*complexSampleMatrix z i j =
      (((z ((i,j),0)^2+z ((i,j),1)^2)/2 : ℝ) : ℂ) := by
    rw [RCLike.star_def,RCLike.conj_mul]
    norm_cast
    rw [RCLike.norm_sq_eq_def]
    simp [complexSampleMatrix]
    field_simp [hn]
    rw [hq]
    ring
  simp only [complexGram,Matrix.mul_apply,Matrix.conjTranspose_apply]
  simp_rw [he]
  rw [← Complex.ofReal_sum]
  rfl

private theorem weighted_gram_coordinates {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (v : Fin n → ℝ) (z : ComplexSample (m := m) (n := n)) :
    (∑ j : Fin n,v j*(complexGram (complexSampleMatrix z+M) j j).re) =
      ∑ a : (Fin m × Fin n) × Fin 2,v a.1.2*(z a+complexSampleMean M a)^2/2 := by
  rw [← complexSampleMatrix_add_mean]
  simp_rw [sample_gram_diagonal]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  change v j*(((z ((i,j),0)+complexSampleMean M ((i,j),0))^2+
    (z ((i,j),1)+complexSampleMean M ((i,j),1))^2)/2) = _
  ring

theorem actualNoncentralDiagonalGram_integral_exp {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (v : Fin n → ℝ) (hv : ∀ j,v j<1) :
    (∫ z : ComplexSample (m := m) (n := n),
      Real.exp (∑ j : Fin n,v j*(complexGram (complexSampleMatrix z+M) j j).re)
      ∂stdGaussian (ComplexSample (m := m) (n := n))) =
      (∏ a : Fin m × Fin n,(1-v a.2)⁻¹)*
        Real.exp (∑ a : Fin m × Fin n,‖M a.1 a.2‖^2*v a.2/(1-v a.2)) := by
  simp_rw [weighted_gram_coordinates]
  rw [← map_pi_eq_stdGaussian,integral_map (by fun_prop) (by fun_prop)]
  let u : ((Fin m × Fin n) × Fin 2) → ℝ := fun a => complexSampleMean M a
  let t : ((Fin m × Fin n) × Fin 2) → ℝ := fun a => v a.1.2
  change (∫ x : ((Fin m × Fin n) × Fin 2) → ℝ,
    Real.exp (∑ a,t a*(x a+u a)^2/2) ∂Measure.pi (fun _ => gaussianReal 0 1))=_
  rw [gaussianPi_integral_exp_weighted_shifted_squares u t (fun a => hv a.1.2)]
  have hp : (∏ a : ((Fin m × Fin n) × Fin 2),(Real.sqrt (1-t a))⁻¹)=
      ∏ a : Fin m × Fin n,(1-v a.2)⁻¹ := by
    rw [Fintype.prod_prod_type]
    apply Finset.prod_congr rfl
    intro a _
    simp only [t,Fin.prod_univ_two]
    rw [← pow_two,inv_pow,Real.sq_sqrt (sub_pos.mpr (hv a.2)).le]
  have he : (∑ a : ((Fin m × Fin n) × Fin 2),(u a)^2*t a/(2*(1-t a)))=
      ∑ a : Fin m × Fin n,‖M a.1 a.2‖^2*v a.2/(1-v a.2) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    have hn : 1-v a.2≠0 := (sub_pos.mpr (hv a.2)).ne'
    simp [u,t,Fin.sum_univ_two,complexSampleMean,RCLike.norm_sq_eq_def,mul_pow]
    <;> field_simp
    <;> ring
  rw [hp,he]

theorem actualNoncentralDiagonalGram_integrable_exp {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (v : Fin n → ℝ) (hv : ∀ j,v j<1) :
    Integrable (fun z : ComplexSample (m := m) (n := n) =>
      Real.exp (∑ j : Fin n,v j*(complexGram (complexSampleMatrix z+M) j j).re))
      (stdGaussian (ComplexSample (m := m) (n := n))) := by
  apply Integrable.of_integral_ne_zero
  rw [actualNoncentralDiagonalGram_integral_exp M v hv]
  apply ne_of_gt
  apply mul_pos
  · apply Finset.prod_pos
    intro a _
    exact inv_pos.2 (sub_pos.mpr (hv a.2))
  · exact Real.exp_pos _

end
end JinWishart
#print axioms JinWishart.actualNoncentralDiagonalGram_integral_exp
#print axioms JinWishart.actualNoncentralDiagonalGram_integrable_exp
