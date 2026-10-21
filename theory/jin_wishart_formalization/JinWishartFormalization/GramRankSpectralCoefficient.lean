import JinWishartFormalization.HermitianSpectralLogDet
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.Algebra.Polynomial.BigOperators

/-! Deterministic Gram rank coefficient; no probability claims.
Codex. Empty matrices and zero eigenvalues are retained. -/
open Matrix Polynomial
open ComplexOrder
namespace JinWishart
noncomputable section

theorem hermitian_det_one_add_complex_smul {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (c : ℂ) :
    (1+c • A).det = ∏ i, (1+c*(hA.eigenvalues i : ℂ)) := by
  classical
  let U := hA.eigenvectorUnitary
  let D : Matrix (Fin n) (Fin n) ℂ := diagonal (RCLike.ofReal ∘ hA.eigenvalues)
  have he : 1+c • A = Unitary.conjStarAlgAut ℂ _ U (1+c • D) := by
    rw [map_add,map_one,map_smul]
    rw [← hA.spectral_theorem]
  have hu := congrArg Matrix.det (Unitary.coe_mul_star_self U)
  simp only [Matrix.det_mul,Matrix.det_one] at hu
  rw [Unitary.coe_star] at hu
  have hd : (1+c • D).det = ∏ i, (1+c*(hA.eigenvalues i : ℂ)) := by
    have hdiag : 1+c • D = diagonal (fun i => 1+c*(hA.eigenvalues i : ℂ)) := by
      ext i j
      by_cases hij : i=j
      · subst j
        simp [D,Matrix.add_apply,Matrix.smul_apply,Matrix.diagonal_apply]
      · simp [D,Matrix.add_apply,Matrix.smul_apply,Matrix.diagonal_apply,Matrix.one_apply,hij]
    rw [hdiag,Matrix.det_diagonal]
  rw [he,Unitary.conjStarAlgAut_apply,Matrix.det_mul,Matrix.det_mul]
  calc
    _ = (1+c • D).det * ((U : Matrix (Fin n) (Fin n) ℂ).det*
        (star (U : Matrix (Fin n) (Fin n) ℂ)).det) := by ring
    _ = (1+c • D).det := by rw [hu,mul_one]
    _ = _ := hd

theorem hermitian_det_polynomial_eq_product {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) :
    (1+(Polynomial.X : ℂ[X]) • A.map Polynomial.C).det =
      ∏ i, (1+Polynomial.C (hA.eigenvalues i : ℂ)*Polynomial.X) := by
  classical
  apply Polynomial.funext
  intro c
  change (Polynomial.evalRingHom c) ((1+(Polynomial.X : ℂ[X]) • A.map Polynomial.C).det) =
    (Polynomial.evalRingHom c) (∏ i, (1+Polynomial.C (hA.eigenvalues i : ℂ)*Polynomial.X))
  rw [RingHom.map_det]
  have hm : (1+(Polynomial.X : ℂ[X]) • A.map Polynomial.C).map (Polynomial.evalRingHom c) =
      1+c • A := by
    ext i j
    change Polynomial.eval c ((if i=j then (1 : ℂ[X]) else 0)+
      Polynomial.X*Polynomial.C (A i j)) = (if i=j then (1 : ℂ) else 0)+c*A i j
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_C]
    congr 1
    split_ifs <;> simp
  change ((1+(Polynomial.X : ℂ[X]) • A.map Polynomial.C).map (Polynomial.evalRingHom c)).det = _
  rw [hm,hermitian_det_one_add_complex_smul A hA]
  change (∏ i, (1+c*(hA.eigenvalues i : ℂ))) =
    Polynomial.eval c (∏ i, (1+Polynomial.C (hA.eigenvalues i : ℂ)*Polynomial.X))
  simp only [Polynomial.eval_prod,Polynomial.eval_add,Polynomial.eval_one,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_X]
  apply Finset.prod_congr rfl
  intro i hi
  ring

theorem gram_rank_coefficient_eq_nonzero_product {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) :
    ((1+(Polynomial.X : ℂ[X]) • (complexGram A).map Polynomial.C).det).coeff A.rank =
      ∏ i ∈ Finset.univ.filter (fun i => (complexGram_posSemidef A).1.eigenvalues i ≠ 0),
        ((complexGram_posSemidef A).1.eigenvalues i : ℂ) := by
  classical
  let hA := (complexGram_posSemidef A).1
  let S := Finset.univ.filter (fun i => hA.eigenvalues i ≠ 0)
  let p := fun i => (1+Polynomial.C (hA.eigenvalues i : ℂ)*Polynomial.X : ℂ[X])
  have hp : (∏ i, p i) = ∏ i ∈ S, p i := by
    symm
    apply Finset.prod_subset (Finset.filter_subset _ _)
    intro i hi hni
    have hz : hA.eigenvalues i = 0 := by simpa [S] using hni
    simp [p,hz]
  have hc : S.card = A.rank := by
    calc
      S.card = Fintype.card {i : Fin n // hA.eigenvalues i ≠ 0} := by
        simp [S,Fintype.card_subtype]
      _ = (complexGram A).rank := hA.rank_eq_card_non_zero_eigs.symm
      _ = A.rank := Matrix.rank_conjTranspose_mul_self A
  rw [hermitian_det_polynomial_eq_product _ hA]
  change (∏ i, p i).coeff A.rank = _
  rw [hp,← hc]
  have hd : ∀ i ∈ S, (p i).natDegree ≤ 1 := by
    intro i hi
    exact (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) (by
      exact Polynomial.natDegree_mul_le.trans (by simp)))
  simpa [p,S,hA,Polynomial.coeff_one] using Polynomial.coeff_prod_of_natDegree_le S p 1 hd

theorem gram_rank_coefficient_re_pos {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) :
    0 < (((1+(Polynomial.X : ℂ[X]) • (complexGram A).map Polynomial.C).det).coeff A.rank).re := by
  classical
  rw [gram_rank_coefficient_eq_nonzero_product]
  have he : (∏ i ∈ Finset.univ.filter (fun i => (complexGram_posSemidef A).1.eigenvalues i ≠ 0),
      ((complexGram_posSemidef A).1.eigenvalues i : ℂ)) =
      ((∏ i ∈ Finset.univ.filter (fun i => (complexGram_posSemidef A).1.eigenvalues i ≠ 0),
        (complexGram_posSemidef A).1.eigenvalues i : ℝ) : ℂ) := by simp
  rw [he,Complex.ofReal_re]
  apply Finset.prod_pos
  intro i hi
  exact lt_of_le_of_ne ((complexGram_posSemidef A).eigenvalues_nonneg i)
    (Ne.symm (Finset.mem_filter.mp hi).2)

theorem gram_rank_coefficient_log_eq_positive_sum {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) :
    Real.log (((1+(Polynomial.X : ℂ[X]) • (complexGram A).map Polynomial.C).det).coeff A.rank).re =
      ∑ i, (if 0 < (complexGram_posSemidef A).1.eigenvalues i then
        Real.log ((complexGram_posSemidef A).1.eigenvalues i) else 0) := by
  classical
  rw [gram_rank_coefficient_eq_nonzero_product]
  have he : (∏ i ∈ Finset.univ.filter (fun i => (complexGram_posSemidef A).1.eigenvalues i ≠ 0),
      ((complexGram_posSemidef A).1.eigenvalues i : ℂ)) =
      ((∏ i ∈ Finset.univ.filter (fun i => (complexGram_posSemidef A).1.eigenvalues i ≠ 0),
        (complexGram_posSemidef A).1.eigenvalues i : ℝ) : ℂ) := by simp
  rw [he,Complex.ofReal_re,Real.log_prod (fun i hi => (Finset.mem_filter.mp hi).2)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hz : (complexGram_posSemidef A).1.eigenvalues i=0
  · simp [hz]
  · have hp := lt_of_le_of_ne ((complexGram_posSemidef A).eigenvalues_nonneg i) (Ne.symm hz)
    simp [hz,hp]

end
end JinWishart
#print axioms JinWishart.hermitian_det_one_add_complex_smul
#print axioms JinWishart.hermitian_det_polynomial_eq_product
#print axioms JinWishart.gram_rank_coefficient_eq_nonzero_product
#print axioms JinWishart.gram_rank_coefficient_re_pos
#print axioms JinWishart.gram_rank_coefficient_log_eq_positive_sum
