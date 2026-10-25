import JinWishartFormalization.ChristoffelMomentDeterminant
import Mathlib.Algebra.Polynomial.Derivative

/-! Codex. Seed2026102502 exact controls precede source. Complex bilinear,
not Hermitian, moment determinants. No positivity or invertibility premise.
[需人工审查] Later factorial/model/paper specialization, not asserted here. -/
open Matrix Polynomial
namespace JinWishart
noncomputable section

private theorem functional_border_det (n : ℕ) (F L : ℂ[X] →ₗ[ℂ] ℂ)
    (p : ℂ[X]) (ho : ∀ i : Fin n,F (X^i.val*p)=0) :
    Matrix.det (fun i j : Fin (n+1) =>
      ((Fin.cases L (fun i => F.comp (LinearMap.mulLeft ℂ (X^i.val))) : Fin (n+1) → ℂ[X] →ₗ[ℂ] ℂ) i)
      (Fin.lastCases p (fun j => X^j.val) j)) =
      (-1 : ℂ)^n*L p*Matrix.det (fun i j : Fin n => F (X^(i.val+j.val))) := by
  classical
  let G : Fin (n+1) → ℂ[X] →ₗ[ℂ] ℂ := Fin.cases L
    (fun i => F.comp (LinearMap.mulLeft ℂ (X^i.val)))
  let P : Fin (n+1) → ℂ[X] := Fin.lastCases p (fun j => X^j.val)
  have hminor : (Matrix.of (fun i j : Fin (n+1) => G i (P j))).submatrix Fin.succ Fin.castSucc =
      Matrix.of (fun i j : Fin n => F (X^(i.val+j.val))) := by
    ext i j
    simp [G,P,Matrix.submatrix_apply,← pow_add]
  change (Matrix.of (fun i j : Fin (n+1) => G i (P j))).det=_
  rw [Matrix.det_succ_column _ (Fin.last n),Fin.sum_univ_succ]
  simp only [Fin.succAbove_zero,Fin.succAbove_last]
  rw [hminor]
  simp [G,P,ho]
  exact Or.inl rfl

private theorem two_functional_border_det (n : ℕ) (F E D : ℂ[X] →ₗ[ℂ] ℂ)
    (p q : ℂ[X]) (hp : ∀ i : Fin n,F (X^i.val*p)=0)
    (hq : ∀ i : Fin n,F (X^i.val*q)=0) :
    Matrix.det (fun i j : Fin (n+2) =>
      ((Fin.cases E (Fin.cases D (fun i => F.comp (LinearMap.mulLeft ℂ (X^i.val))))) : Fin (n+2) → ℂ[X] →ₗ[ℂ] ℂ) i
      (Fin.lastCases q (Fin.lastCases p (fun j => X^j.val)) j)) =
      (E p*D q-E q*D p)*Matrix.det (fun i j : Fin n => F (X^(i.val+j.val))) := by
  classical
  let G : Fin (n+2) → ℂ[X] →ₗ[ℂ] ℂ := Fin.cases E
    (Fin.cases D (fun i => F.comp (LinearMap.mulLeft ℂ (X^i.val))))
  let P : Fin (n+2) → ℂ[X] := Fin.lastCases q (Fin.lastCases p (fun j => X^j.val))
  let M : Matrix (Fin (n+2)) (Fin (n+2)) ℂ := fun i j => G i (P j)
  have hminor0 : M.submatrix Fin.succ Fin.castSucc =
      Matrix.of (fun i j : Fin (n+1) =>
        ((Fin.cases D (fun i => F.comp (LinearMap.mulLeft ℂ (X^i.val)))) : Fin (n+1) → ℂ[X] →ₗ[ℂ] ℂ) i
        (Fin.lastCases p (fun j => X^j.val) j)) := by
    ext i j
    change G i.succ (P j.castSucc)=_
    simp [G,P]
  have hminor1 : M.submatrix ((0 : Fin (n+1)).succ.succAbove) Fin.castSucc =
      Matrix.of (fun i j : Fin (n+1) =>
        ((Fin.cases E (fun i => F.comp (LinearMap.mulLeft ℂ (X^i.val)))) : Fin (n+1) → ℂ[X] →ₗ[ℂ] ℂ) i
        (Fin.lastCases p (fun j => X^j.val) j)) := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i
    · change G ((0 : Fin (n+1)).succ.succAbove 0) (P j.castSucc)=_
      rw [Fin.succAbove_succ_self]
      simp [G,P]
    · change G ((0 : Fin (n+1)).succ.succAbove i.succ) (P j.castSucc)=_
      rw [Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def])]
      simp [G,P]
  change M.det=_
  rw [Matrix.det_succ_column M (Fin.last (n+1)),Fin.sum_univ_succ]
  simp only [Fin.succAbove_zero,Fin.succAbove_last]
  rw [Fin.sum_univ_succ]
  have hz (i : Fin n) : M i.succ.succ (Fin.last (n+1))=0 := by simp [M,G,P,hq]
  simp only [hz,mul_zero,zero_mul,Finset.sum_const_zero,add_zero]
  rw [hminor0,hminor1]
  simp only [Fin.val_zero,Fin.val_last,Fin.val_succ,zero_add]
  dsimp only [Matrix.of,M,G,P,Fin.cases_zero,Fin.cases_succ]
  simp only [Fin.lastCases_last,Equiv.refl_apply]
  change (-1 : ℂ)^(n+1)*(E q)*Matrix.det (fun i j : Fin (n+1) =>
      ((Fin.cases D (fun i => F.comp (LinearMap.mulLeft ℂ (X^i.val)))) : Fin (n+1) → ℂ[X] →ₗ[ℂ] ℂ) i
      (Fin.lastCases p (fun j => X^j.val) j))+
    (-1 : ℂ)^(1+(n+1))*(D q)*Matrix.det (fun i j : Fin (n+1) =>
      ((Fin.cases E (fun i => F.comp (LinearMap.mulLeft ℂ (X^i.val)))) : Fin (n+1) → ℂ[X] →ₗ[ℂ] ℂ) i
      (Fin.lastCases p (fun j => X^j.val) j))=_
  rw [functional_border_det n F D p hp,functional_border_det n F E p hp]
  have hs : (-1 : ℂ)^(n+1)*(-1)^n = -1 := by
    rw [← pow_add,show n+1+n=2*n+1 by omega,pow_add,pow_mul]
    norm_num
  have ht : (-1 : ℂ)^(1+(n+1))*(-1)^n = 1 := by
    rw [← pow_add,show 1+(n+1)+n=2*(n+1) by omega,pow_mul]
    norm_num
  calc
    _ = ((-1 : ℂ)^(n+1)*(-1)^n)*(E q*D p*Matrix.det (fun i j : Fin n => F (X^(i.val+j.val))))+
        ((-1 : ℂ)^(1+(n+1))*(-1)^n)*(D q*E p*Matrix.det (fun i j : Fin n => F (X^(i.val+j.val)))) := by ring
    _ = _ := by rw [hs,ht];ring

theorem quadratic_christoffel_moment_det (n : ℕ) (F : ℂ[X] →ₗ[ℂ] ℂ) (p q : ℂ[X])
    (hdp : p.natDegree=n) (hmp : p.Monic) (hdq : q.natDegree=n+1) (hmq : q.Monic)
    (hp : ∀ i : Fin n,F (X^i.val*p)=0) (hq : ∀ i : Fin n,F (X^i.val*q)=0) (z : ℂ) :
    Matrix.det (fun i j : Fin n => F ((X-C z)^2*X^(i.val+j.val))) =
      Matrix.det (fun i j : Fin n => F (X^(i.val+j.val)))*
        (p.eval z*(Polynomial.derivative q).eval z-q.eval z*(Polynomial.derivative p).eval z) := by
  classical
  let E : ℂ[X] →ₗ[ℂ] ℂ := Polynomial.leval z
  let D : ℂ[X] →ₗ[ℂ] ℂ := E.comp Polynomial.derivative
  let G : Fin (n+2) → ℂ[X] →ₗ[ℂ] ℂ := Fin.cases E
    (Fin.cases D (fun i => F.comp (LinearMap.mulLeft ℂ (X^i.val))))
  let Q : Fin (n+2) → ℂ[X] := Fin.cases 1
    (Fin.cases (X-C z) (fun j => (X-C z)^2*X^j.val))
  let P : Fin (n+2) → ℂ[X] := Fin.lastCases q (Fin.lastCases p (fun j => X^j.val))
  have hdQ (j : Fin (n+2)) : (Q j).natDegree=j.val := by
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [Q]
    · refine Fin.cases ?_ (fun j => ?_) j
      · change (X-C z : ℂ[X]).natDegree=1
        simp
      · change ((X-C z)^2*X^j.val : ℂ[X]).natDegree=j.val+1+1
        simp [Polynomial.natDegree_mul,(monic_X_sub_C z).ne_zero,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
  have hmQ (j : Fin (n+2)) : (Q j).Monic := by
    refine Fin.cases ?_ (fun j => ?_) j
    · exact monic_one
    · refine Fin.cases ?_ (fun j => ?_) j
      · exact monic_X_sub_C z
      · exact ((monic_X_sub_C z).pow 2).mul (monic_X_pow _)
  have hdP (j : Fin (n+2)) : (P j).natDegree=j.val := by
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa [P] using hdq
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa [P] using hdp
      · simp [P]
  have hmP (j : Fin (n+2)) : (P j).Monic := by
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa [P] using hmq
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa [P] using hmp
      · simpa [P] using monic_X_pow (R := ℂ) j.val
  have hQ : Matrix.det (fun i j : Fin (n+2) => G i (Q j)) =
      Matrix.det (fun i j : Fin n => F ((X-C z)^2*X^(i.val+j.val))) := by
    let M : Matrix (Fin (n+2)) (Fin (n+2)) ℂ := fun i j => G i (Q j)
    have hminor : (M.submatrix Fin.succ Fin.succ).submatrix Fin.succ Fin.succ =
        Matrix.of (fun i j : Fin n => F ((X-C z)^2*X^(i.val+j.val))) := by
      ext i j
      change F (X^i.val*((X-C z)^2*X^j.val))=F ((X-C z)^2*X^(i.val+j.val))
      congr 1
      rw [pow_add]
      ring
    change M.det=_
    rw [Matrix.det_succ_row_zero M,Fin.sum_univ_succ]
    have he (j : Fin (n+1)) : M 0 j.succ=0 := by
      change Polynomial.eval z (Fin.cases (X-C z) (fun j => (X-C z)^2*X^j.val) j)=0
      refine Fin.cases ?_ (fun j => ?_) j
      · change Polynomial.eval z (X-C z)=0
        simp
      · change Polynomial.eval z ((X-C z)^2*X^j.val)=0
        simp
    simp only [he,mul_zero,zero_mul,Finset.sum_const_zero,add_zero]
    have he0 : M 0 0=1 := by simp [M,G,E,Q,Polynomial.leval_apply]
    rw [he0]
    simp only [Fin.val_zero,pow_zero,one_mul,Fin.succAbove_zero]
    rw [Matrix.det_succ_row_zero,Fin.sum_univ_succ]
    have hd (j : Fin n) : (M.submatrix Fin.succ Fin.succ) 0 j.succ=0 := by
      change Polynomial.eval z (Polynomial.derivative ((X-C z)^2*X^j.val))=0
      simp [Polynomial.derivative_mul,Polynomial.derivative_pow]
    simp only [hd,mul_zero,zero_mul,Finset.sum_const_zero,add_zero]
    have hd0 : (M.submatrix Fin.succ Fin.succ) 0 0=1 := by
      change Polynomial.eval z (Polynomial.derivative (X-C z))=1
      simp
    rw [hd0]
    have hm : (M.submatrix Fin.succ Fin.succ).submatrix Fin.succ Fin.succ =
        (fun i j : Fin n => F ((X-C z)^2*X^(i.val+j.val))) := by
      ext i j
      exact congrFun (congrFun hminor i) j
    simpa only [Fin.val_zero,pow_zero,one_mul,Fin.succAbove_zero] using congrArg Matrix.det hm
  have hP := two_functional_border_det n F E D p q hp hq
  have hb := (monic_functional_columns_det (n+2) G Q hdQ hmQ).trans
    (monic_functional_columns_det (n+2) G P hdP hmP).symm
  rw [hQ] at hb
  rw [hb]
  change Matrix.det (fun i j : Fin (n+2) =>
    ((Fin.cases E (Fin.cases D (fun i => F.comp (LinearMap.mulLeft ℂ (X^i.val))))) : Fin (n+2) → ℂ[X] →ₗ[ℂ] ℂ) i
      (Fin.lastCases q (Fin.lastCases p (fun j => X^j.val)) j))=_
  rw [hP]
  simp [E,D,Polynomial.leval_apply,mul_comm]

end
end JinWishart
#print axioms JinWishart.quadratic_christoffel_moment_det
