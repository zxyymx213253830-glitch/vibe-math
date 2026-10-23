import JinWishartFormalization.ActualCanonicalInverseTransport

/-! Original-source sharp inverse criterion after eliminating explicit fixed
canonical data. Full stacked column rank and a nontrivial nonsurjective
noiseless kernel image are explicit. Codex. Controls: seed2026102235,
512 exact shapes/1537 checks; existing physical and distribution controls reused.
[需人工审查] Actual Gaussian source, AE spectral boundary, measure transport.
Common-kernel compression and zero-block edge branches are not claimed here. -/
open Matrix Module MeasureTheory ProbabilityTheory
namespace JinWishart
noncomputable section

private theorem detUnitOfBijective {n : ℕ} (N : Matrix (Fin n) (Fin n) ℂ)
    (hN : Function.Bijective N.toEuclideanLin) : IsUnit N.det := by
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  have hh : N.toEuclideanLin (WithLp.toLp 2 x)=N.toEuclideanLin (WithLp.toLp 2 y) :=
    congrArg (WithLp.toLp 2) hxy
  exact congrArg (fun z : EuclideanSpace ℂ (Fin n) => (⇑z)) (hN.1 hh)

theorem actual_full_stack_inverse_realMoment_integrable_iff {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (hstack : (Matrix.fromRows B M).rank=n) (hb : 0<B.rank)
    (hc : 0<finrank ℂ B.toEuclideanLin.ker)
    (hcm : finrank ℂ B.toEuclideanLin.ker<m)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=min m n)
    (q : ℝ) (hq : 0<q) :
    Integrable (fun z => (actualCorrelatedEigenvalue B M i z)⁻¹^q)
      (stdGaussian (ComplexSample (m := m) (n := p))) ↔
      q<((max m n-min m n+1 : ℕ) : ℝ) := by
  have hjoint : Function.Injective (B.toEuclideanLin.prod M.toEuclideanLin) := by
    simpa only [Matrix.mul_one] using correlated_fixed_compression_joint_injective
      B M (1 : Matrix (Fin n) (Fin n) ℂ) hstack.symm (by simp) (by simp)
  obtain ⟨b,c,a,T,U,V,N,MA,MH,hb',hc',hbc,hac,hT,hU,hBT,hN,hMean⟩ :=
    exists_joint_kernel_canonical_matrix B M hjoint
  have hb0 : 0<b := by omega
  have hc0 : 0<c := by omega
  have ha0 : 0<a := by omega
  let er : (Fin a ⊕ Fin c) ≃ Fin m := finSumFinEquiv.trans (finCongr hac)
  let ec : (Fin b ⊕ Fin c) ≃ Fin n := finSumFinEquiv.trans (finCongr hbc)
  have hab : 0<min a b := lt_min ha0 hb0
  let j : Fin (Fintype.card (Fin b)) := ⟨min a b-1,by simp only [Fintype.card_fin]; omega⟩
  have hj : j.val+1=min a b := by dsimp [j]; omega
  let k : Fin (Fintype.card (Fin c)) := ⟨c-1,by simp only [Fintype.card_fin]; omega⟩
  have hk : k.val+1=c := by dsimp [k]; omega
  have hshape : max a b-min a b+1=max m n-min m n+1 := by
    rcases le_total a b with h|h <;> rcases le_total m n with g|g <;>
      simp only [Nat.max_eq_right h,Nat.min_eq_left h,Nat.max_eq_left h,
        Nat.min_eq_right h,Nat.max_eq_right g,Nat.min_eq_left g,
        Nat.max_eq_left g,Nat.min_eq_right g] <;> omega
  have hcrit := actual_canonical_inverse_realMoment_integrable_iff ha0 hb0 hc0
    B M T U V MA MH N er ec hBT hU hMean hT (detUnitOfBijective N hN)
    hstack i hi j hj k hk q hq
  simpa only [hshape] using hcrit

theorem actual_full_stack_inverse_realMoment_lintegral_eq_top {m p n : ℕ}
    (B : Matrix (Fin p) (Fin n) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (hstack : (Matrix.fromRows B M).rank=n) (hb : 0<B.rank)
    (hc : 0<finrank ℂ B.toEuclideanLin.ker)
    (hcm : finrank ℂ B.toEuclideanLin.ker<m)
    (i : Fin (Fintype.card (Fin n))) (hi : i.val+1=min m n)
    (q : ℝ) (hq : ((max m n-min m n+1 : ℕ) : ℝ)≤q) :
    (∫⁻ z : ComplexSample (m := m) (n := p),
      ENNReal.ofReal ((actualCorrelatedEigenvalue B M i z)⁻¹^q) ∂stdGaussian _)=⊤ := by
  have hq0 : 0<q := lt_of_lt_of_le
    (by positivity : (0 : ℝ)<((max m n-min m n+1 : ℕ) : ℝ)) hq
  have hF : Measurable (fun z => (actualCorrelatedEigenvalue B M i z)⁻¹^q) :=
    (measurable_actualCorrelatedEigenvalue B M i).inv.pow_const q
  by_contra h
  have hI := (lintegral_ofReal_ne_top_iff_integrable hF.aestronglyMeasurable
    (ae_of_all _ (fun z => Real.rpow_nonneg (inv_nonneg.mpr
      (complexGram_eigenvalues₀_nonneg (complexSampleMatrix z*B+M) i)) q))).mp h
  exact (not_lt_of_ge hq) ((actual_full_stack_inverse_realMoment_integrable_iff
    B M hstack hb hc hcm i hi q hq0).mp hI)

end
end JinWishart
#print axioms JinWishart.actual_full_stack_inverse_realMoment_integrable_iff
#print axioms JinWishart.actual_full_stack_inverse_realMoment_lintegral_eq_top
