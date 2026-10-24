import JinWishartFormalization.PolynomialMomentTranslation
import Mathlib.Algebra.Polynomial.Eval.SMul

/-! Codex. Seed2026102404 complex-functional controls before source.
Finite bilinear algebra only. No positive measure or multiplicativity premise.
[需人工审查] Sign conventions when instantiated for original T1. -/
open Matrix Polynomial
namespace JinWishart
noncomputable section

theorem monic_functional_columns_det (n : ℕ) (G : Fin n → ℂ[X] →ₗ[ℂ] ℂ)
    (p : Fin n → ℂ[X]) (hd : ∀ i,(p i).natDegree=i.val) (hm : ∀ i,(p i).Monic) :
    Matrix.det (fun i j : Fin n => G i (p j)) =
      Matrix.det (fun i j : Fin n => G i (X^j.val)) := by
  classical
  let T : Matrix (Fin n) (Fin n) ℂ := fun i j => (p i).coeff j.val
  let B : Matrix (Fin n) (Fin n) ℂ := fun i j => G i (X^j.val)
  have hp (j : Fin n) : p j=∑ k : Fin n,(p j).coeff k.val • (X : ℂ[X])^k.val := by
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => (p j).coeff k • (X : ℂ[X])^k) n]
    simpa only [smul_eq_C_mul] using
      (p j).as_sum_range_C_mul_X_pow' (by rw [hd];exact j.isLt)
  have hT : T.det=1 := by
    rw [← Matrix.det_transpose]
    exact Matrix.det_matrixOfPolynomials p hd hm
  have he : Matrix.of (fun i j : Fin n => G i (p j))=B*T.transpose := by
    ext i j
    rw [Matrix.mul_apply]
    change G i (p j)=∑ k : Fin n,G i (X^k.val)*(p j).coeff k.val
    rw [hp j,map_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp [map_smul,mul_comm]
  change (Matrix.of (fun i j : Fin n => G i (p j))).det=B.det
  rw [he,Matrix.det_mul,Matrix.det_transpose,hT,mul_one]

theorem christoffel_moment_det (n : ℕ) (F : ℂ[X] →ₗ[ℂ] ℂ) (p : ℂ[X])
    (hd : p.natDegree=n) (hm : p.Monic)
    (ho : ∀ i : Fin n,F (X^i.val*p)=0) (z : ℂ) :
    Matrix.det (fun i j : Fin n => F ((X-C z)*X^(i.val+j.val))) =
      (-1 : ℂ)^n*p.eval z*Matrix.det (fun i j : Fin n => F (X^(i.val+j.val))) := by
  classical
  let G : Fin (n+1) → ℂ[X] →ₗ[ℂ] ℂ := Fin.cases (Polynomial.leval z)
    (fun i => F.comp (LinearMap.mulLeft ℂ ((X : ℂ[X])^i.val)))
  let Q : Fin (n+1) → ℂ[X] := Fin.cases 1 (fun j => X^j.val*(X-C z))
  let P : Fin (n+1) → ℂ[X] := Fin.lastCases p (fun j => X^j.val)
  have hdQ (j : Fin (n+1)) : (Q j).natDegree=j.val := by
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [Q]
    · simp [Q,Polynomial.natDegree_mul, (monic_X_sub_C z).ne_zero]
  have hmQ (j : Fin (n+1)) : (Q j).Monic := by
    refine Fin.cases ?_ (fun j => ?_) j
    · exact monic_one
    · exact (monic_X_pow _).mul (monic_X_sub_C z)
  have hdP (j : Fin (n+1)) : (P j).natDegree=j.val := by
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa [P] using hd
    · simp [P]
  have hmP (j : Fin (n+1)) : (P j).Monic := by
    refine Fin.lastCases ?_ (fun j => ?_) j
    · exact hm
    · exact monic_X_pow _
  have hQ : Matrix.det (fun i j : Fin (n+1) => G i (Q j))=
      Matrix.det (fun i j : Fin n => F ((X-C z)*X^(i.val+j.val))) := by
    rw [Matrix.det_succ_row_zero,Fin.sum_univ_succ]
    simp [G,Q,Polynomial.leval_apply,Matrix.submatrix_apply,pow_add,mul_comm,mul_left_comm,mul_assoc]
  have hP : Matrix.det (fun i j : Fin (n+1) => G i (P j))=
      (-1 : ℂ)^n*p.eval z*Matrix.det (fun i j : Fin n => F (X^(i.val+j.val))) := by
    rw [Matrix.det_succ_column _ (Fin.last n),Fin.sum_univ_succ]
    simp [G,P,Polynomial.leval_apply,ho,Matrix.submatrix_apply,← pow_add]
  exact hQ.symm.trans ((monic_functional_columns_det (n+1) G Q hdQ hmQ).trans
    ((monic_functional_columns_det (n+1) G P hdP hmP).symm.trans hP))

end
end JinWishart
#print axioms JinWishart.monic_functional_columns_det
#print axioms JinWishart.christoffel_moment_det
