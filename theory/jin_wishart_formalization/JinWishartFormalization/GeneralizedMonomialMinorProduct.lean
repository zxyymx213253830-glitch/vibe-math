import JinWishartFormalization.GeneralizedMonomialVandermondePos
import Mathlib.Data.Finset.Sort

/-! Codex. Seed2026102702:698 exact minor-pair controls before source.
Both determinants acquire the same permutation sign; their product is positive.
These are finite minor products, not a full finite/infinite Bessel-kernel theorem.
[需人工审查] Simultaneous ordering, determinant orientation and later transport. -/
open Matrix Finset Function
namespace JinWishart
noncomputable section

private theorem sorted_exponents_permutation (n : ℕ) (k : Fin n → ℕ)
 (hk : Injective k) : ∃ (g : Fin n → ℕ) (σ : Equiv.Perm (Fin n)),
 StrictMono g ∧ ∀ i, k i = g (σ i) := by
 let S := Finset.univ.image k
 have hc : S.card = n := by
   simpa [S] using Finset.card_image_of_injective Finset.univ hk
 let f : Fin n → S := fun i => ⟨k i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
 have hf : Bijective f := by
   constructor
   · intro i j hij
     exact hk (congrArg Subtype.val hij)
   · intro y
     obtain ⟨i,_,hi⟩ := Finset.mem_image.mp y.property
     exact ⟨i,Subtype.ext hi⟩
 let e := Equiv.ofBijective f hf
 let o := S.orderIsoOfFin hc
 refine ⟨fun i => (o i : ℕ),e.trans o.toEquiv.symm,?_,?_⟩
 · intro i j hij
   exact o.strictMono hij
 · intro i
   exact (congrArg Subtype.val (o.apply_symm_apply (e i))).symm

theorem generalizedMonomialMinorProduct_pos (n : ℕ) (k : Fin n → ℕ)
 (x y : Fin n → ℝ) (hk : Injective k) (hx : StrictMono x) (hy : StrictMono y)
 (hxp : ∀ i, 0 < x i) (hyp : ∀ i, 0 < y i) :
 0 < (Matrix.of (fun i j : Fin n => x i ^ k j)).det *
     (Matrix.of (fun i j : Fin n => y i ^ k j)).det := by
 obtain ⟨g,σ,hg,hkg⟩ := sorted_exponents_permutation n k hk
 let A : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun i j => x i ^ g j)
 let B : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun i j => y i ^ g j)
 have ha : Matrix.of (fun i j : Fin n => x i ^ k j) = A.submatrix id σ := by
   ext i j
   simp [A,hkg]
 have hb : Matrix.of (fun i j : Fin n => y i ^ k j) = B.submatrix id σ := by
   ext i j
   simp [B,hkg]
 rw [ha,hb,Matrix.det_permute',Matrix.det_permute']
 have hs : ((Equiv.Perm.sign σ : ℤ) : ℝ)*((Equiv.Perm.sign σ : ℤ) : ℝ) = 1 := by
   exact_mod_cast Int.isUnit_mul_self (Equiv.Perm.sign σ).isUnit
 have he : ((Equiv.Perm.sign σ : ℤ) : ℝ)*A.det *
     (((Equiv.Perm.sign σ : ℤ) : ℝ)*B.det) = A.det*B.det := by
   calc
     _ = (((Equiv.Perm.sign σ : ℤ) : ℝ)*((Equiv.Perm.sign σ : ℤ) : ℝ))*(A.det*B.det) := by ring
     _ = _ := by rw [hs,one_mul]
 rw [he]
 exact mul_pos (generalizedMonomialVandermonde_det_pos n g x hg hx hxp)
   (generalizedMonomialVandermonde_det_pos n g y hg hy hyp)

theorem weightedGeneralizedMonomialMinorProduct_pos (n : ℕ) (k : Fin n → ℕ)
 (x y w : Fin n → ℝ) (hk : Injective k) (hx : StrictMono x) (hy : StrictMono y)
 (hxp : ∀ i, 0 < x i) (hyp : ∀ i, 0 < y i) (hw : ∀ i, 0 < w i) :
 0 < (Matrix.of (fun i j : Fin n => x i ^ k j)).det *
     (Matrix.of (fun i j : Fin n => w i * y j ^ k i)).det := by
 have hs : (Matrix.of (fun i j : Fin n => w i * y j ^ k i)).det =
     (∏ i : Fin n, w i)*(Matrix.of (fun i j : Fin n => y j ^ k i)).det := by
   convert Matrix.det_mul_column w (Matrix.of (fun i j : Fin n => y j ^ k i)) using 1
 rw [hs]
 have ht : (Matrix.of (fun i j : Fin n => y j ^ k i)).det =
     (Matrix.of (fun i j : Fin n => y i ^ k j)).det := by
   rw [← Matrix.det_transpose]
   rfl
 rw [ht]
 have hp := generalizedMonomialMinorProduct_pos n k x y hk hx hy hxp hyp
 have hwp : 0 < ∏ i : Fin n, w i := Finset.prod_pos (fun i _ => hw i)
 convert mul_pos hwp hp using 1 <;> ring

theorem weightedGeneralizedMonomialMinorProduct_nonneg (n : ℕ) (k : Fin n → ℕ)
 (x y w : Fin n → ℝ) (hx : StrictMono x) (hy : StrictMono y)
 (hxp : ∀ i, 0 < x i) (hyp : ∀ i, 0 < y i) (hw : ∀ i, 0 < w i) :
 0 ≤ (Matrix.of (fun i j : Fin n => x i ^ k j)).det *
     (Matrix.of (fun i j : Fin n => w i * y j ^ k i)).det := by
 by_cases hk : Injective k
 · exact (weightedGeneralizedMonomialMinorProduct_pos n k x y w hk hx hy hxp hyp hw).le
 · simp only [Injective] at hk
   push_neg at hk
   obtain ⟨i,j,hij,hne⟩ := hk
   have hz : (Matrix.of (fun i j : Fin n => x i ^ k j)).det = 0 := by
     rw [← Matrix.det_transpose]
     apply Matrix.det_zero_of_row_eq hne
     funext l
     exact congrArg (fun a => x l ^ a) hij
   rw [hz,zero_mul]

end
end JinWishart
#print axioms JinWishart.generalizedMonomialMinorProduct_pos
#print axioms JinWishart.weightedGeneralizedMonomialMinorProduct_pos
#print axioms JinWishart.weightedGeneralizedMonomialMinorProduct_nonneg
