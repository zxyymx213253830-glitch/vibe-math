import JinWishartFormalization.SplitAndreiefCountGenerating
import Mathlib.Algebra.Polynomial.Roots

/-! Count coefficients for the split Andreief determinant. Codex.
No assumed Wishart density is identified here. [需人工审查] Product L1 and finite partition. -/
open MeasureTheory Finset Matrix Polynomial
namespace JinWishart
noncomputable section
variable {n : ℕ} {μ : Measure ℝ} [SigmaFinite μ]

theorem measurable_coordinateMembershipCount (E : Set ℝ) (hE : MeasurableSet E) :
    Measurable (coordinateMembershipCount (n := n) E) := by
  classical
  have he : coordinateMembershipCount (n := n) E=
      fun z => ∑ i : Fin n,if z i ∈ E then (1 : ℕ) else 0 := by
    funext z
    simp only [coordinateMembershipCount,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [he]
  exact Finset.measurable_sum _ (fun i _ => measurable_const.ite
    (hE.preimage (measurable_pi_apply i)) measurable_const)

theorem andreief_det_product_integrable (f g : Fin n → ℝ → ℝ)
    (hfg : ∀ i j,Integrable (fun y => f i y*g j y) μ) :
    Integrable (fun z : Fin n → ℝ =>
      (Matrix.of (fun i j => f i (z j))).det*(Matrix.of (fun i j => g i (z j))).det)
        (Measure.pi (fun _ : Fin n => μ)) := by
  classical
  have hi (σ τ : Equiv.Perm (Fin n)) : Integrable
      (fun z : Fin n → ℝ => (Equiv.Perm.sign σ : ℝ)*(Equiv.Perm.sign τ : ℝ)*
        ((∏ i,f (σ i) (z i))*(∏ i,g (τ i) (z i)))) (Measure.pi (fun _ : Fin n => μ)) := by
    have he : (fun z : Fin n → ℝ => (∏ i,f (σ i) (z i))*(∏ i,g (τ i) (z i)))=
        fun z => ∏ i,f (σ i) (z i)*g (τ i) (z i) := by
      funext z
      exact (Finset.prod_mul_distrib).symm
    apply Integrable.const_mul
    rw [he]
    exact Integrable.fintype_prod (fun i => hfg (σ i) (τ i))
  have hp (z : Fin n → ℝ) :
      (Matrix.of (fun i j => f i (z j))).det*(Matrix.of (fun i j => g i (z j))).det=
      ∑ τ : Equiv.Perm (Fin n),∑ σ : Equiv.Perm (Fin n),
        (Equiv.Perm.sign σ : ℝ)*(Equiv.Perm.sign τ : ℝ)*
          ((∏ i,f (σ i) (z i))*(∏ i,g (τ i) (z i))) := by
    rw [Matrix.det_apply',Matrix.det_apply',Finset.sum_mul_sum,Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro τ _
    apply Finset.sum_congr rfl
    intro σ _
    simp only [Matrix.of_apply]
    ring
  simp_rw [hp]
  exact integrable_finsetSum _ (fun τ _ => integrable_finsetSum _ (fun σ _ => hi σ τ))

def countDeterminantMoment (f g : Fin n → ℝ → ℝ) (μ : Measure ℝ)
    (E : Set ℝ) (k : ℕ) : ℝ :=
  ∫ z : Fin n → ℝ in {z | coordinateMembershipCount E z=k},
    (Matrix.of (fun i j => f i (z j))).det*(Matrix.of (fun i j => g i (z j))).det
      ∂(Measure.pi (fun _ : Fin n => μ))

theorem split_andreief_count_polynomial (f g : Fin n → ℝ → ℝ)
    (hfg : ∀ i j,Integrable (fun y => f i y*g j y) μ)
    (E : Set ℝ) (hE : MeasurableSet E) :
    (rowAffinePolynomialMatrix
      (Matrix.of (fun i j => ∫ y in E,f i y*g j y ∂μ))
      (Matrix.of (fun i j => ∫ y in Eᶜ,f i y*g j y ∂μ))).det=
    ∑ k ∈ Finset.range (n+1),Polynomial.C ((1/(n.factorial : ℝ))*countDeterminantMoment f g μ E k)*Polynomial.X^k := by
  classical
  let ν := Measure.pi (fun _ : Fin n => μ)
  let D : (Fin n → ℝ) → ℝ := fun z =>
    (Matrix.of (fun i j => f i (z j))).det*(Matrix.of (fun i j => g i (z j))).det
  have hD : Integrable D ν := andreief_det_product_integrable f g hfg
  have hK (k : ℕ) : MeasurableSet {z : Fin n → ℝ | coordinateMembershipCount E z=k} :=
    measurableSet_eq_fun (measurable_coordinateMembershipCount E hE) measurable_const
  apply Polynomial.funext
  intro t
  have heval : ((rowAffinePolynomialMatrix
      (Matrix.of (fun i j => ∫ y in E,f i y*g j y ∂μ))
      (Matrix.of (fun i j => ∫ y in Eᶜ,f i y*g j y ∂μ))).det).eval t=
      Matrix.det (fun i j => t*(∫ y in E,f i y*g j y ∂μ)+∫ y in Eᶜ,f i y*g j y ∂μ) := by
    change (Polynomial.evalRingHom t) _=_
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp [rowAffinePolynomialMatrix,add_comm]
    ring
  rw [heval,split_andreief_count_generating f g hfg E hE t]
  have hpart (z : Fin n → ℝ) : t^coordinateMembershipCount E z*D z=
      ∑ k ∈ Finset.range (n+1),t^k*{z | coordinateMembershipCount E z=k}.indicator D z := by
    have hc : coordinateMembershipCount E z<n+1 := by
      have := Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun i => z i ∈ E)
      simpa [coordinateMembershipCount] using Nat.lt_succ_of_le this
    rw [Finset.sum_eq_single (coordinateMembershipCount E z)]
    · simp
    · intro k hk hne
      simp [Ne.symm hne]
    · simp [Finset.mem_range,hc]
  simp_rw [mul_assoc]
  change (1/(n.factorial : ℝ))*(∫ z,t^coordinateMembershipCount E z*D z ∂ν)=_
  simp_rw [hpart]
  rw [integral_finsetSum _ (fun k _ => (hD.indicator (hK k)).const_mul (t^k))]
  simp only [Polynomial.eval_finsetSum,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
    Polynomial.eval_X,integral_const_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [integral_indicator (hK k)]
  change (1/(n.factorial : ℝ))*(t^k*countDeterminantMoment f g μ E k)=_
  ring

theorem split_andreief_count_coefficient (f g : Fin n → ℝ → ℝ)
    (hfg : ∀ i j,Integrable (fun y => f i y*g j y) μ)
    (E : Set ℝ) (hE : MeasurableSet E) (k : ℕ) (hk : k≤n) :
    ((rowAffinePolynomialMatrix
      (Matrix.of (fun i j => ∫ y in E,f i y*g j y ∂μ))
      (Matrix.of (fun i j => ∫ y in Eᶜ,f i y*g j y ∂μ))).det).coeff k=
      (1/(n.factorial : ℝ))*countDeterminantMoment f g μ E k := by
  classical
  rw [split_andreief_count_polynomial f g hfg E hE]
  simp only [Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul_X_pow]
  simp [Nat.lt_succ_of_le hk]

theorem split_andreief_count_rowMix (f g : Fin n → ℝ → ℝ)
    (hfg : ∀ i j,Integrable (fun y => f i y*g j y) μ)
    (E : Set ℝ) (hE : MeasurableSet E) (k : ℕ) (hk : k≤n) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      if S.card=k then (rowMix
        (Matrix.of (fun i j => ∫ y in E,f i y*g j y ∂μ))
        (Matrix.of (fun i j => ∫ y in Eᶜ,f i y*g j y ∂μ)) S).det else 0)=
      (1/(n.factorial : ℝ))*countDeterminantMoment f g μ E k := by
  rw [← coeff_det_rowAffinePolynomial_eq_fixedCardRowSum]
  exact split_andreief_count_coefficient f g hfg E hE k hk

end
end JinWishart
#print axioms JinWishart.measurable_coordinateMembershipCount
#print axioms JinWishart.andreief_det_product_integrable
#print axioms JinWishart.split_andreief_count_polynomial

#print axioms JinWishart.split_andreief_count_coefficient
#print axioms JinWishart.split_andreief_count_rowMix
