import JinWishartFormalization.FactorialHankelDeterminant
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Monic

/-! Change of monic polynomial basis preserves a bilinear moment determinant.
Codex. Original159 factorial controls precede this source; the complex
extension201 was run after drafting but before its first kernel check.
This uses transpose, not conjugate transpose; positivity is not assumed. -/
open Matrix Polynomial
namespace JinWishart
noncomputable section

theorem monic_polynomial_moment_det (n : ℕ) (F : ℂ[X] →ₗ[ℂ] ℂ)
    (p : Fin n → ℂ[X]) (hd : ∀ i,(p i).natDegree=i.val) (hm : ∀ i,(p i).Monic) :
    (fun i j : Fin n => F (p i*p j)).det=
      (fun i j : Fin n => F (X^(i.val+j.val))).det := by
  classical
  let T : Matrix (Fin n) (Fin n) ℂ := fun i j => (p i).coeff j.val
  let H : Matrix (Fin n) (Fin n) ℂ := fun i j => F (X^(i.val+j.val))
  have hp (i : Fin n) : p i=∑ k : Fin n,(p i).coeff k.val • (X : ℂ[X])^k.val := by
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => (p i).coeff k • (X : ℂ[X])^k) n]
    simpa only [smul_eq_C_mul] using
      (p i).as_sum_range_C_mul_X_pow' (by rw [hd];exact i.isLt)
  have hdet : T.det=1 := by
    rw [← Matrix.det_transpose]
    exact Matrix.det_matrixOfPolynomials p hd hm
  have heq : (fun i j : Fin n => F (p i*p j))=T*H*T.transpose := by
    ext i j
    rw [Matrix.mul_assoc,Matrix.mul_apply]
    change F (p i*p j)=∑ k : Fin n,(p i).coeff k.val*
      (∑ l : Fin n,F (X^(k.val+l.val))*(p j).coeff l.val)
    rw [hp i,hp j]
    simp only [Finset.sum_mul,Finset.mul_sum,map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    simp only [smul_mul_assoc,mul_smul_comm,smul_smul,map_smul,RingHom.id_apply,
      ← pow_add,smul_eq_mul]
    ring
  rw [heq,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,hdet,one_mul,mul_one]

theorem shifted_polynomial_moment_det (n : ℕ) (F : ℂ[X] →ₗ[ℂ] ℂ) (x : ℂ) :
    (fun i j : Fin n => F ((X+C x)^(i.val+j.val))).det=
      (fun i j : Fin n => F (X^(i.val+j.val))).det := by
  have hd (i : Fin n) : ((X+C x)^(i.val) : ℂ[X]).natDegree=i.val := by
    simp
  have hm (i : Fin n) : ((X+C x)^(i.val) : ℂ[X]).Monic := (monic_X_add_C x).pow _
  simpa only [← pow_add] using
    monic_polynomial_moment_det n F (fun i => (X+C x)^i.val) hd hm

end
end JinWishart
#print axioms JinWishart.monic_polynomial_moment_det
#print axioms JinWishart.shifted_polynomial_moment_det
