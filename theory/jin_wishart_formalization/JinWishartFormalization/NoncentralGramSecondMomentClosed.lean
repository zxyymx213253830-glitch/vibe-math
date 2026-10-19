import JinWishartFormalization.NoncentralGramEntryContraction

/-! Closed second trace moment for actual noncentral complex Gaussian Gram matrices.
Codex. [需人工审查] Actual expectation/variance correspondence inherited.
-/
open Matrix MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace JinWishart
noncomputable section

theorem complexGaussianMoment_noncentralGramSquaredTrace_closed {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) :
    complexGaussianPolynomialMoment (noncentralGramSquaredTracePolynomial M) =
      ((m*n*(m+n) : ℕ) : ℂ)+2*((m+n : ℕ) : ℂ)*(complexGram M).trace+((complexGram M)^2).trace := by
  classical
  have hL (P : ComplexMatrixPolynomial m n) :
      complexGaussianMomentLinear P = complexGaussianPolynomialMoment P := rfl
  have hs : complexGaussianPolynomialMoment (noncentralGramSquaredTracePolynomial M) =
      ∑ i, ∑ j, ∑ k, ∑ l,
      (star (M k i)*M k j*star (M l j)*M l i +
        (if i=j then 1 else 0)*(M l i*star (M l i)+M k i*star (M k i)) +
        (if k=l then 1 else 0)*(M k j*star (M k j)+M k i*star (M k i)) +
        (if i=j then 1 else 0)+(if k=l then 1 else 0)) := by
    change complexGaussianMomentLinear (noncentralGramSquaredTracePolynomial M) = _
    unfold noncentralGramSquaredTracePolynomial
    simp only [pow_two,Matrix.trace,Matrix.diag,Matrix.mul_apply,noncentralGramEntryPolynomial,
      Finset.sum_mul,Finset.mul_sum]
    simp only [map_sum]
    simp only [hL,noncentralGram_entry_fourth_contraction]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact Finset.sum_comm
  rw [hs]
  simp only [Finset.sum_add_distrib]
  have hmean : (∑ i, ∑ j, ∑ k, ∑ l, star (M k i)*M k j*star (M l j)*M l i) =
      ((complexGram M)^2).trace := by
    simp only [pow_two,complexGram,Matrix.trace,Matrix.diag,Matrix.mul_apply,
      Matrix.conjTranspose_apply,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    simp only [RCLike.star_def]
    ring
  rw [hmean]
  have hcol (i : Fin n) :
      (∑ j, ∑ k, ∑ l, (if i=j then (1 : ℂ) else 0)*
        (M l i*star (M l i)+M k i*star (M k i))) =
      ∑ k, ∑ l, (M l i*star (M l i)+M k i*star (M k i)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_comm]
    simp
  simp_rw [hcol]
  simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
    Finset.sum_ite_irrel,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    ← Finset.mul_sum,← Finset.sum_mul]
  have htrace : (∑ i, ∑ k, M k i*star (M k i)) = (complexGram M).trace := by
    simp only [complexGram,Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    simp only [RCLike.star_def]
    ring
  rw [htrace]
  push_cast
  simp
  ring

theorem complexGaussianMoment_noncentralGramSquaredTrace_re_closed {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) :
    (complexGaussianPolynomialMoment (noncentralGramSquaredTracePolynomial M)).re =
      ((m*n*(m+n) : ℕ) : ℝ)+2*((m+n : ℕ) : ℝ)*(∑ i, ∑ j, ‖M i j‖^2)+
        ((complexGram M)^2).trace.re := by
  have h := congrArg Complex.re (complexGaussianMoment_noncentralGramSquaredTrace_closed M)
  norm_num [Complex.add_re,Complex.mul_re,Complex.mul_im] at h
  rw [complexGram_trace_re] at h
  simpa only [Nat.cast_mul,Nat.cast_add] using h

theorem integral_actualNoncentralGram_squaredTrace_closed {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) :
    (∫ z : ComplexSample (m := m) (n := n), ((complexGram (complexSampleMatrix z+M))^2).trace.re
      ∂stdGaussian _) =
      ((m*n*(m+n) : ℕ) : ℝ)+2*((m+n : ℕ) : ℝ)*(∑ i, ∑ j, ‖M i j‖^2)+
        ((complexGram M)^2).trace.re := by
  rw [integral_actualNoncentralGram_squaredTrace]
  exact complexGaussianMoment_noncentralGramSquaredTrace_re_closed M

theorem actualNoncentralMatrixLogDet_low_scale_closed_curvature {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) :
    Tendsto (fun r : ℝ =>
      (r*((m*n : ℕ)+∑ i, ∑ j, ‖M i j‖^2)-
        (∫ z, actualNoncentralMatrixLogDet M r z ∂stdGaussian _))/r^2)
      (𝓝[>] 0)
      (𝓝 ((((m*n*(m+n) : ℕ) : ℝ)+2*((m+n : ℕ) : ℝ)*(∑ i, ∑ j, ‖M i j‖^2)+
        ((complexGram M)^2).trace.re)/2)) := by
  simpa only [complexGaussianMoment_noncentralGramSquaredTrace_re_closed] using
    actualNoncentralMatrixLogDet_low_scale_finite_curvature M

end
end JinWishart
#print axioms JinWishart.complexGaussianMoment_noncentralGramSquaredTrace_closed
#print axioms JinWishart.complexGaussianMoment_noncentralGramSquaredTrace_re_closed
#print axioms JinWishart.integral_actualNoncentralGram_squaredTrace_closed
#print axioms JinWishart.actualNoncentralMatrixLogDet_low_scale_closed_curvature
