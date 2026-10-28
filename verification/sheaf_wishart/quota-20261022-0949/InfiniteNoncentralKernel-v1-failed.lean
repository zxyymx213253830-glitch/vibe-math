import JinWishartFormalization.FiniteNoncentralKernel
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Instances.Matrix

/-! Codex. Seed2026102802:540 high-precision Bessel/series/fixed-floor controls
precede source. Strict positivity uses a uniform positive finite-minor floor,
not the invalid assertion that every positive sequence has a positive limit.
Full noncentral-rank entire series only; no actual Wishart joint law.
[需人工审查] Series comparison, finite matrix limit and later model mapping. -/
open Matrix Finset Filter
open scoped Topology
namespace JinWishart
noncomputable section

private theorem kernel_series_summable (q : ℕ) (x lambda : ℝ)
 (hx : 0 ≤ x) (hl : 0 ≤ lambda) :
 Summable (fun m : ℕ => x^m*(noncentralKernelSeriesWeight q m*lambda^m)) := by
 let z := x*lambda
 have hz : 0 ≤ z := mul_nonneg hx hl
 have hg (m : ℕ) : 0 ≤ z^m/(m.factorial : ℝ)/((q+m).factorial : ℝ) := by
   positivity
 have hle (m : ℕ) : z^m/(m.factorial : ℝ)/((q+m).factorial : ℝ) ≤
     z^m/(m.factorial : ℝ) := by
   apply div_le_self (by positivity)
   have hh : 1 ≤ (q+m).factorial := Nat.factorial_pos _
   exact_mod_cast hh
 have hs := Summable.of_nonneg_of_le hg hle (Real.summable_pow_div_factorial z)
 have he (m : ℕ) : x^m*(noncentralKernelSeriesWeight q m*lambda^m) =
     z^m/(m.factorial : ℝ)/((q+m).factorial : ℝ) := by
   dsimp [z]
   simp only [noncentralKernelSeriesWeight,mul_pow,mul_inv_rev,div_eq_mul_inv]
   ring
 exact hs.congr (fun m => (he m).symm)

def noncentralFullSeriesKernel (q n : ℕ) (x lambda : Fin n → ℝ) :
 Matrix (Fin n) (Fin n) ℝ :=
 Matrix.of (fun i j => ∑' m : ℕ,
   x i ^ m * (noncentralKernelSeriesWeight q m * lambda j ^ m))

theorem finiteNoncentralFullKernel_tendsto (q n : ℕ) (x lambda : Fin n → ℝ)
 (hxp : ∀ i, 0 ≤ x i) (hlp : ∀ i, 0 ≤ lambda i) :
 Tendsto (fun N : ℕ => finiteNoncentralFullKernel q n N x lambda) atTop
   (𝓝 (noncentralFullSeriesKernel q n x lambda)) := by
 apply tendsto_pi_nhds.mpr
 intro i
 apply tendsto_pi_nhds.mpr
 intro j
 change Tendsto (fun N : ℕ => ∑ m : Fin N,
   x i ^ m.val * (noncentralKernelSeriesWeight q m.val * lambda j ^ m.val)) atTop
     (𝓝 (∑' m : ℕ, x i ^ m * (noncentralKernelSeriesWeight q m * lambda j ^ m)))
 simpa only [Fin.sum_univ_eq_sum_range] using
   (kernel_series_summable q (x i) (lambda j) (hxp i) (hlp j)).hasSum.tendsto_sum_nat

theorem noncentralFullSeriesKernel_det_lower_bound (q n : ℕ) (x lambda : Fin n → ℝ)
 (hx : StrictMono x) (hl : StrictMono lambda)
 (hxp : ∀ i, 0 < x i) (hlp : ∀ i, 0 < lambda i) :
 noncentralKernelLowestMinor q n x lambda ≤
   (n.factorial : ℝ)*(noncentralFullSeriesKernel q n x lambda).det := by
 have hc : Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => A.det) := continuous_id.matrix_det
 have hd : Tendsto (fun N : ℕ => (finiteNoncentralFullKernel q n N x lambda).det) atTop
     (𝓝 (noncentralFullSeriesKernel q n x lambda).det) := by
   convert (hc.tendsto (noncentralFullSeriesKernel q n x lambda)).comp
     (finiteNoncentralFullKernel_tendsto q n x lambda (fun i => (hxp i).le) (fun i => (hlp i).le)) using 1 <;> rfl
 have hs := hd.const_mul (n.factorial : ℝ)
 apply ge_of_tendsto hs
 filter_upwards [eventually_ge_atTop n] with N hN
 exact finiteNoncentralFullKernel_det_lower_bound q n N hN x lambda hx hl hxp hlp

theorem noncentralFullSeriesKernel_det_pos (q n : ℕ) (x lambda : Fin n → ℝ)
 (hx : StrictMono x) (hl : StrictMono lambda)
 (hxp : ∀ i, 0 < x i) (hlp : ∀ i, 0 < lambda i) :
 0 < (noncentralFullSeriesKernel q n x lambda).det := by
 have hc : 0 < noncentralKernelLowestMinor q n x lambda :=
   weightedGeneralizedMonomialMinorProduct_pos n (fun i : Fin n => i.val)
     x lambda (fun i => noncentralKernelSeriesWeight q i.val) Fin.val_injective
       hx hl hxp hlp (fun i => by unfold noncentralKernelSeriesWeight; positivity)
 have hb := noncentralFullSeriesKernel_det_lower_bound q n x lambda hx hl hxp hlp
 have hp : 0 < (n.factorial : ℝ) := by positivity
 exact (mul_pos_iff_of_pos_left hp).mp (lt_of_lt_of_le hc hb)

end
end JinWishart
#print axioms JinWishart.finiteNoncentralFullKernel_tendsto
#print axioms JinWishart.noncentralFullSeriesKernel_det_lower_bound
#print axioms JinWishart.noncentralFullSeriesKernel_det_pos
