import JinWishartFormalization.TwoRowHermitianThreshold
import JinWishartFormalization.TwoByTwoTraceCoordinates

/-! Codex. Seed2026102405: signed Hermitian spectral controls before source.
All Hermitian 2x2 matrices, including repeated eigenvalues and indefinite matrices.
No joint probability density is assumed or concluded. [需人工审查] Ordering convention. -/
open Matrix
namespace JinWishart
noncomputable section

def twoRowTracelessRadius (A : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  ‖(WithLp.toLp 2 ![((A 0 0).re-(A 1 1).re)/2,(A 0 1).re,(A 0 1).im] :
    EuclideanSpace ℝ (Fin 3))‖

theorem hermitian_twoRow_ordered_eigenpair (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A.IsHermitian) :
    hA.eigenvalues₀ 0=((A 0 0).re+(A 1 1).re)/2+twoRowTracelessRadius A ∧
    hA.eigenvalues₀ 1=((A 0 0).re+(A 1 1).re)/2-twoRowTracelessRadius A := by
  classical
  let e : Fin (Fintype.card (Fin 2)) ≃ Fin 2 :=
    Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin 2)))
  have hs : (∑ j,hA.eigenvalues₀ j)=∑ j,hA.eigenvalues j := by
    simpa only [Matrix.IsHermitian.eigenvalues,e,Equiv.symm_apply_apply] using
      (Equiv.sum_comp e (fun j => hA.eigenvalues j))
  have hp : (∏ j,hA.eigenvalues₀ j)=∏ j,hA.eigenvalues j := by
    simpa only [Matrix.IsHermitian.eigenvalues,e,Equiv.symm_apply_apply] using
      (Equiv.prod_comp e (fun j => hA.eigenvalues j))
  have ht : (A 0 0).re+(A 1 1).re=hA.eigenvalues 0+hA.eigenvalues 1 := by
    simpa [Matrix.trace,Fin.sum_univ_two,RCLike.ofReal_eq_complex_ofReal] using
      congrArg Complex.re hA.trace_eq_sum_eigenvalues
  have hd : A.det.re=hA.eigenvalues 0*hA.eigenvalues 1 := by
    simpa [Fin.prod_univ_two,RCLike.ofReal_eq_complex_ofReal] using
      congrArg Complex.re hA.det_eq_prod_eigenvalues
  have hsum : hA.eigenvalues₀ 0+hA.eigenvalues₀ 1=(A 0 0).re+(A 1 1).re := by
    simp only [Fin.sum_univ_two] at hs
    exact hs.trans ht.symm
  have hprod : hA.eigenvalues₀ 0*hA.eigenvalues₀ 1=A.det.re := by
    simp only [Fin.prod_univ_two] at hp
    exact hp.trans hd.symm
  have hr : (twoRowTracelessRadius A)^2=
      (((A 0 0).re-(A 1 1).re)/2)^2+(A 0 1).re^2+(A 0 1).im^2 := by
    simp [twoRowTracelessRadius,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_succ,add_assoc]
  have hr0 : 0≤twoRowTracelessRadius A := norm_nonneg _
  have ho : hA.eigenvalues₀ 1≤hA.eigenvalues₀ 0 := hA.eigenvalues₀_antitone (by decide)
  have hg : (hA.eigenvalues₀ 0-hA.eigenvalues₀ 1)^2=(2*twoRowTracelessRadius A)^2 := by
    rw [hermitian_twoRow_det_re A hA] at hprod
    nlinarith [congrArg (fun x : ℝ => x^2) hsum,hprod,hr]
  have he := (sq_eq_sq₀ (sub_nonneg.mpr ho) (by positivity : 0≤2*twoRowTracelessRadius A)).mp hg
  constructor <;> linarith

end
end JinWishart
#print axioms JinWishart.hermitian_twoRow_ordered_eigenpair
