import JinWishartFormalization.InfiniteMixedNoncentralKernel
import JinWishartFormalization.BesselProductKernel

/-! Codex. Seed 2026102903 supplied 580 Bessel/factorization controls before
source. Central columns are multiplied by the common positive row factor;
the noncentral columns use the real part of the actual Bessel definition.
No actual Wishart law is asserted. [需人工审查] Scaling and model mapping. -/
open Matrix Finset
namespace JinWishart
noncomputable section

def mixedBesselColumnFactor (p L q : ℕ) (lambda : Fin L → ℝ) : Fin (p+L) → ℝ :=
 fun j => match (finSumFinEquiv (m := p) (n := L)).symm j with
 | Sum.inl _ => 1
 | Sum.inr b => (Real.sqrt (lambda b))^q

def mixedBesselKernel (p L q : ℕ) (x : Fin (p+L) → ℝ)
 (lambda : Fin L → ℝ) : Matrix (Fin (p+L)) (Fin (p+L)) ℝ :=
 Matrix.of (fun i j => match (finSumFinEquiv (m := p) (n := L)).symm j with
 | Sum.inl a => (Real.sqrt (x i))^q * x i ^ a.val
 | Sum.inr b => (modifiedBesselI q ((2*Real.sqrt (x i*lambda b) : ℝ) : ℂ)).re)

theorem mixedBesselKernel_factorization (p L q : ℕ) (x : Fin (p+L) → ℝ)
 (lambda : Fin L → ℝ) (hx : ∀ i, 0 ≤ x i) (hl : ∀ i, 0 ≤ lambda i) :
 mixedBesselKernel p L q x lambda =
 Matrix.of (fun i j => (Real.sqrt (x i))^q *
   (mixedBesselColumnFactor p L q lambda j * infiniteMixedKernel p L q x lambda i j)) := by
 ext i j
 cases hj : (finSumFinEquiv (m := p) (n := L)).symm j with
 | inl a => simp [mixedBesselKernel,mixedBesselColumnFactor,infiniteMixedKernel,hj]
 | inr b =>
   simp only [mixedBesselKernel,mixedBesselColumnFactor,infiniteMixedKernel,
     Matrix.of_apply,hj]
   exact modifiedBesselI_sqrt_product_re q (x i) (lambda b) (hx i) (hl b)

theorem mixedBesselKernel_det_pos (p L q : ℕ) (x : Fin (p+L) → ℝ)
 (lambda : Fin L → ℝ) (hx : StrictMono x) (hxp : ∀ i, 0 < x i)
 (hl : StrictMono lambda) (hlp : ∀ i, 0 < lambda i) :
 0 < (mixedBesselKernel p L q x lambda).det := by
 let K := infiniteMixedKernel p L q x lambda
 let r : Fin (p+L) → ℝ := fun i => (Real.sqrt (x i))^q
 let c : Fin (p+L) → ℝ := mixedBesselColumnFactor p L q lambda
 have hR := Matrix.det_mul_column r (Matrix.of (fun i j => c j*K i j))
 have hC := Matrix.det_mul_row c K
 have hd : (mixedBesselKernel p L q x lambda).det =
     (∏ i : Fin (p+L), r i)*(∏ j : Fin (p+L), c j)*K.det := by
   rw [mixedBesselKernel_factorization p L q x lambda (fun i => (hxp i).le) (fun i => (hlp i).le)]
   calc
     _ = (∏ i : Fin (p+L), r i)*(Matrix.of (fun i j => c j*K i j)).det := by
       convert hR using 1 <;> rfl
     _ = _ := by rw [hC]; ring
 rw [hd]
 have hr : 0 < ∏ i : Fin (p+L), r i :=
   Finset.prod_pos (fun i _ => pow_pos (Real.sqrt_pos.mpr (hxp i)) q)
 have hc : 0 < ∏ j : Fin (p+L), c j := by
   apply Finset.prod_pos
   intro j hj
   dsimp [c,mixedBesselColumnFactor]
   split
   · exact zero_lt_one
   · exact pow_pos (Real.sqrt_pos.mpr (hlp _)) q
 exact mul_pos (mul_pos hr hc) (infiniteMixedKernel_det_pos p L q x lambda hx hxp hl hlp)

end
end JinWishart
#print axioms JinWishart.mixedBesselKernel_factorization
#print axioms JinWishart.mixedBesselKernel_det_pos
