import JinWishartFormalization.FiniteMixedNoncentralKernel
import JinWishartFormalization.InfiniteNoncentralKernel

/-! Codex. Seed 2026102901 exact mixed finite controls and earlier seed
2026102802 series controls precede source. A fixed finite minor persists
through the matrix limit. This is a formula-side kernel, not an actual law.
[需人工审查] Central-column extraction, matrix convergence and model mapping. -/
open Matrix Finset Filter
open scoped Topology
namespace JinWishart
noncomputable section

def infiniteMixedKernel (p L q : ℕ) (x : Fin (p+L) → ℝ)
 (lambda : Fin L → ℝ) : Matrix (Fin (p+L)) (Fin (p+L)) ℝ :=
 Matrix.of (fun i j => match (finSumFinEquiv (m := p) (n := L)).symm j with
 | Sum.inl a => x i ^ a.val
 | Sum.inr b => ∑' m : ℕ, x i ^ m * (noncentralKernelSeriesWeight q m * lambda b ^ m))

private theorem finiteMixed_central_entry (p L N q : ℕ) (hpN : p ≤ N)
 (x : Fin (p+L) → ℝ) (lambda : Fin L → ℝ) (i : Fin (p+L)) (a : Fin p) :
 finiteMixedKernel p L N x lambda (noncentralKernelSeriesWeight q) i
   (finSumFinEquiv (Sum.inl a)) = x i ^ a.val := by
 let aN : Fin N := ⟨a.val, by omega⟩
 simp only [finiteMixedKernel,Matrix.mul_apply,Matrix.of_apply,Equiv.symm_apply_apply]
 change (∑ m : Fin N, x i ^ m.val *
   mixedKernelCoefficient p L N lambda (noncentralKernelSeriesWeight q) m (Sum.inl a)) = _
 rw [Finset.sum_eq_single aN]
 · simp [mixedKernelCoefficient,aN]
 · intro m hm hne
   have hmne : m.val ≠ a.val := by
     intro he
     apply hne
     exact Fin.ext he
   simp [mixedKernelCoefficient,hmne]
 · intro ha
   exact False.elim (ha (Finset.mem_univ aN))

private theorem finiteMixed_noncentral_entry (p L N q : ℕ)
 (x : Fin (p+L) → ℝ) (lambda : Fin L → ℝ) (i : Fin (p+L)) (b : Fin L) :
 finiteMixedKernel p L N x lambda (noncentralKernelSeriesWeight q) i
   (finSumFinEquiv (Sum.inr b)) =
 finiteNoncentralFullKernel q (p+L) N x (fun _ => lambda b) i
   (finSumFinEquiv (Sum.inr b)) := by
 simp [finiteMixedKernel,finiteNoncentralFullKernel,Matrix.mul_apply,mixedKernelCoefficient]

theorem finiteMixedKernel_tendsto (p L q : ℕ) (x : Fin (p+L) → ℝ)
 (lambda : Fin L → ℝ) (hxp : ∀ i, 0 ≤ x i) (hlp : ∀ i, 0 ≤ lambda i) :
 Tendsto (fun N : ℕ => finiteMixedKernel p L N x lambda (noncentralKernelSeriesWeight q))
   atTop (𝓝 (infiniteMixedKernel p L q x lambda)) := by
 apply tendsto_pi_nhds.mpr
 intro i
 apply tendsto_pi_nhds.mpr
 intro j
 let e := finSumFinEquiv (m := p) (n := L)
 cases hj : e.symm j with
 | inl a =>
   have hje : j = e (Sum.inl a) := by
     have h := e.apply_symm_apply j
     rw [hj] at h
     exact h.symm
   rw [hje]
   simp only [infiniteMixedKernel,Matrix.of_apply]
   simp only [show finSumFinEquiv.symm (e (Sum.inl a)) = Sum.inl a by simp [e]]
   have ht : Tendsto (fun _N : ℕ => x i ^ a.val) atTop (𝓝 (x i ^ a.val)) := tendsto_const_nhds
   apply ht.congr'
   filter_upwards [eventually_ge_atTop p] with N hN
   exact (finiteMixed_central_entry p L N q hN x lambda i a).symm
 | inr b =>
   have hje : j = e (Sum.inr b) := by
     have h := e.apply_symm_apply j
     rw [hj] at h
     exact h.symm
   rw [hje]
   simp only [infiniteMixedKernel,Matrix.of_apply]
   simp only [show finSumFinEquiv.symm (e (Sum.inr b)) = Sum.inr b by simp [e]]
   have ht := finiteNoncentralFullKernel_tendsto q (p+L) x (fun _ => lambda b)
     hxp (fun _ => hlp b)
   have hi := (tendsto_pi_nhds.mp ht) i
   have hij := (tendsto_pi_nhds.mp hi) (e (Sum.inr b))
   change Tendsto (fun N : ℕ => finiteMixedKernel p L N x lambda
     (noncentralKernelSeriesWeight q) i (e (Sum.inr b))) atTop
     (𝓝 (∑' m : ℕ, x i ^ m * (noncentralKernelSeriesWeight q m * lambda b ^ m)))
   apply hij.congr'
   exact Filter.Eventually.of_forall (fun N =>
     (finiteMixed_noncentral_entry p L N q x lambda i b).symm)

theorem infiniteMixedKernel_det_lower_bound (p L q : ℕ) (x : Fin (p+L) → ℝ)
 (lambda : Fin L → ℝ) (hx : StrictMono x) (hxp : ∀ i, 0 < x i)
 (hl : StrictMono lambda) (hlp : ∀ i, 0 < lambda i) :
 mixedLowestMinor p L x lambda (noncentralKernelSeriesWeight q) ≤
   ((p+L).factorial : ℝ)*(infiniteMixedKernel p L q x lambda).det := by
 have hc : Continuous (fun A : Matrix (Fin (p+L)) (Fin (p+L)) ℝ => A.det) := continuous_id.matrix_det
 have hd := (hc.tendsto (infiniteMixedKernel p L q x lambda)).comp
   (finiteMixedKernel_tendsto p L q x lambda (fun i => (hxp i).le) (fun i => (hlp i).le))
 have hs := hd.const_mul ((p+L).factorial : ℝ)
 apply ge_of_tendsto hs
 filter_upwards [eventually_ge_atTop (p+L)] with N hN
 exact finiteMixedKernel_det_lower_bound p L N hN x lambda (noncentralKernelSeriesWeight q)
   hx hxp hl hlp (fun m => by unfold noncentralKernelSeriesWeight; positivity)

theorem infiniteMixedKernel_det_pos (p L q : ℕ) (x : Fin (p+L) → ℝ)
 (lambda : Fin L → ℝ) (hx : StrictMono x) (hxp : ∀ i, 0 < x i)
 (hl : StrictMono lambda) (hlp : ∀ i, 0 < lambda i) :
 0 < (infiniteMixedKernel p L q x lambda).det := by
 have hc := mixedLowestMinor_pos p L x lambda (noncentralKernelSeriesWeight q)
   hx hxp hl hlp (fun m => by unfold noncentralKernelSeriesWeight; positivity)
 have hb := infiniteMixedKernel_det_lower_bound p L q x lambda hx hxp hl hlp
 have hp : 0 < ((p+L).factorial : ℝ) := by positivity
 exact (mul_pos_iff_of_pos_left hp).mp (lt_of_lt_of_le hc hb)

end
end JinWishart
#print axioms JinWishart.finiteMixedKernel_tendsto
#print axioms JinWishart.infiniteMixedKernel_det_lower_bound
#print axioms JinWishart.infiniteMixedKernel_det_pos
