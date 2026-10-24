import JinWishartFormalization.FactorialLaguerreOrthogonality
import JinWishartFormalization.ChristoffelMomentDeterminant
import JinWishartFormalization.CentralGammaDenominator
import JinWishartFormalization.RectangularWishartOneExtraRow

/-! Codex. Seed2026102403 controls before source.
All-size one-surplus factorial/Gamma determinants, no actual CDF assumed.
[需人工审查] Later original T1 indexing and probability mapping. -/
open Matrix Polynomial
namespace JinWishart
noncomputable section

private theorem factorialProduct_shift_one (n : ℕ) :
    (n.factorial : ℂ)*(∏ i : Fin n,(i.val.factorial : ℂ)^2)=
      ∏ i : Fin n,(i.val.factorial : ℂ)*((i.val+1).factorial : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Fin.prod_univ_castSucc,Fin.val_castSucc,Fin.val_last]
    rw [← ih]
    simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    ring

theorem factorialHankel_one_surplus_pencil_det (n : ℕ) (x : ℂ) :
    Matrix.det (fun i j : Fin n => ((i.val+j.val+1).factorial : ℂ)+x*((i.val+j.val).factorial : ℂ)) =
      (∏ i : Fin n,(i.val.factorial : ℂ)*((i.val+1).factorial : ℂ))*
        ∑ k ∈ Finset.range (n+1),(n.choose k : ℂ)*x^k/(k.factorial : ℂ) := by
  have h := christoffel_moment_det n factorialMomentFunctional (factorialLaguerre n)
    (factorialLaguerre_natDegree n) (factorialLaguerre_monic n)
    (fun i => factorialLaguerre_moment_orthogonal n i.val i.isLt) (-x)
  have hf (i j : Fin n) : factorialMomentFunctional ((X-C (-x))*X^(i.val+j.val)) =
      ((i.val+j.val+1).factorial : ℂ)+x*((i.val+j.val).factorial : ℂ) := by
    rw [map_neg,sub_neg_eq_add,add_mul,←pow_succ',map_add,
      ← smul_eq_C_mul,map_smul,factorialMoment_X_pow,factorialMoment_X_pow]
    rfl
  simp_rw [hf,factorialMoment_X_pow] at h
  change _ = (-1 : ℂ)^n*(factorialLaguerre n).eval (-x)*(factorialHankel n).det at h
  rw [factorialLaguerre_eval_neg,factorialHankel_det] at h
  rw [h,← factorialProduct_shift_one]
  ring

theorem upperGammaHankel_one_surplus_det (n : ℕ) (x : ℝ) (hx : 0≤x) :
    Matrix.det (fun i j : Fin n => upperGammaNat (i.val+j.val+1) x) =
      (Real.exp (-(n : ℝ)*x) : ℂ)*
      (∏ i : Fin n,(i.val.factorial : ℂ)*((i.val+1).factorial : ℂ))*
      (oneExtraRowMinimumPolynomial n x : ℂ) := by
  let F : ℂ[X] →ₗ[ℂ] ℂ := factorialMomentFunctional.comp (LinearMap.mulLeft ℂ (X+C (x : ℂ)))
  have heq : Matrix.of (fun i j : Fin n => upperGammaNat (i.val+j.val+1) x)=
      (Real.exp (-x) : ℂ) • Matrix.of (fun i j : Fin n => F ((X+C (x : ℂ))^(i.val+j.val))) := by
    ext i j
    change upperGammaNat (i.val+j.val+1) x=(Real.exp (-x) : ℂ)*F ((X+C (x : ℂ))^(i.val+j.val))
    rw [upperGammaNat_eq_factorialMoment _ x hx]
    dsimp only [F,LinearMap.comp_apply,LinearMap.mulLeft_apply]
    rw [pow_succ']
  change (Matrix.of (fun i j : Fin n => upperGammaNat (i.val+j.val+1) x)).det=_
  rw [heq,Matrix.det_smul,Fintype.card_fin]
  change (Real.exp (-x) : ℂ)^n*Matrix.det (fun i j : Fin n => F ((X+C (x : ℂ))^(i.val+j.val)))=_
  rw [shifted_polynomial_moment_det]
  have hf (i j : Fin n) : F (X^(i.val+j.val))=
      ((i.val+j.val+1).factorial : ℂ)+(x : ℂ)*((i.val+j.val).factorial : ℂ) := by
    dsimp only [F,LinearMap.comp_apply,LinearMap.mulLeft_apply]
    rw [add_mul,←pow_succ',map_add,←smul_eq_C_mul,map_smul,
      factorialMoment_X_pow,factorialMoment_X_pow]
    rfl
  simp_rw [hf]
  rw [factorialHankel_one_surplus_pencil_det]
  have hexp : (Real.exp (-x) : ℂ)^n=(Real.exp (-(n : ℝ)*x) : ℂ) := by
    rw [←Complex.ofReal_pow,←Real.exp_nat_mul]
    congr 2
    ring
  rw [hexp]
  have hsum : (∑ k ∈ Finset.range (n+1),(n.choose k : ℂ)*(x : ℂ)^k/(k.factorial : ℂ))=
      (oneExtraRowMinimumPolynomial n x : ℂ) := by
    unfold oneExtraRowMinimumPolynomial
    push_cast
    rfl
  rw [hsum]
  ring

end
end JinWishart
#print axioms JinWishart.factorialHankel_one_surplus_pencil_det
#print axioms JinWishart.upperGammaHankel_one_surplus_det
