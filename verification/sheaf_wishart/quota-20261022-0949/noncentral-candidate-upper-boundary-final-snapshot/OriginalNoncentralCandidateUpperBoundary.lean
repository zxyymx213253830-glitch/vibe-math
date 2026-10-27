import JinWishartFormalization.OriginalPsiNormalizerNonzero
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Real.Sqrt

/-! Codex. Seed2026102612:295 calibrated controls precede source.
Upper-threshold limits of the ORIGINAL formula candidates, not actual joint laws.
Natural Nuttall orders here already have true L1 by NoncentralRadialFullMoments;
no divergent improper integral is interpreted as probability.
[需人工审查] Tail integrals, finite matrix continuity and source/model mapping. -/
open Filter MeasureTheory Set Matrix
open scoped Topology
namespace JinWishart
noncomputable section

private theorem natural_nuttall_tail (q k : ℕ) (a : ℝ) :
 Tendsto (fun b : ℝ => nuttallQ (q+2*k+1) q a b) atTop (𝓝 0) := by
 unfold nuttallQ
 exact MeasureTheory.tendsto_integral_Ioi_zero tendsto_id

private theorem gamma_nat_tail (k : ℕ) :
 Tendsto (fun x : ℝ => upperGammaNat k x) atTop (𝓝 0) := by
 have ht : Tendsto (fun x : ℝ => upperGammaTail ((k+1 : ℕ) : ℂ) x) atTop (𝓝 0) := by
   unfold upperGammaTail
   exact MeasureTheory.tendsto_integral_Ioi_zero tendsto_id
 apply ht.congr'
 filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
 exact (upperGammaComplement_eq_tail (s := ((k+1 : ℕ) : ℂ)) (by simp; positivity) hx).symm

theorem theorem1PsiMatrix_tendsto_zero (s t L : ℕ) (hst : s ≤ t) (hLs : L ≤ s)
 (lambda : Fin L → ℝ) :
 Tendsto (fun x : ℝ => theorem1PsiMatrix s t L hst hLs lambda x) atTop
   (𝓝 (0 : Matrix (Fin s) (Fin s) ℂ)) := by
 apply tendsto_pi_nhds.mpr
 intro i
 apply tendsto_pi_nhds.mpr
 intro j
 change Tendsto (fun x : ℝ => theorem1PsiEntry s t L hst hLs lambda i j x) atTop (𝓝 0)
 by_cases hj : j.val < L
 · simp only [theorem1PsiEntry,dite_eq_left hj]
   have ho : theorem1QOrder s t i = (t-s)+2*(s-(i.val+1))+1 := by
     unfold theorem1QOrder
     omega
   rw [ho]
   have hb : Tendsto (fun x : ℝ => Real.sqrt (2*x)) atTop atTop :=
     Real.tendsto_sqrt_atTop.comp
       (Filter.Tendsto.const_mul_atTop (by norm_num : 0 < (2 : ℝ)) tendsto_id)
   simpa only [mul_zero, Function.comp_apply] using
     ((natural_nuttall_tail (t-s) (s-(i.val+1)) (Real.sqrt (2*lambda ⟨j.val,hj⟩))).comp hb).const_mul
       ((Real.rpow 2 ((((2*(i.val+1) : ℕ) : ℝ)-s-t)/2) : ℝ) : ℂ)
 · simpa only [theorem1PsiEntry,dite_eq_right hj] using gamma_nat_tail (theorem1GammaIndex s t i j)

theorem theorem2XiMatrix_tendsto_full (s t L : ℕ) (hst : s ≤ t) (hLs : L ≤ s)
 (lambda : Fin L → ℝ) :
 Tendsto (fun x : ℝ => theorem2XiMatrix s t L hst hLs lambda x) atTop
   (𝓝 (theorem1PsiMatrix s t L hst hLs lambda 0)) := by
 have he : (fun x : ℝ => theorem2XiMatrix s t L hst hLs lambda x) =
   (fun x => theorem1PsiMatrix s t L hst hLs lambda 0 - theorem1PsiMatrix s t L hst hLs lambda x) := by
   funext x
   exact eq_sub_iff_add_eq.mpr (theorem2XiMatrix_add_theorem1PsiMatrix s t L hst hLs lambda x)
 rw [he]
 simpa only [sub_zero] using
   (tendsto_const_nhds.sub (theorem1PsiMatrix_tendsto_zero s t L hst hLs lambda))

theorem theorem1CdfCandidate_tendsto_one (s t L : ℕ) (hs : 0 < s)
 (hst : s ≤ t) (hLs : L ≤ s) (lambda : Fin L → ℝ) :
 Tendsto (fun x : ℝ => theorem1CdfCandidate s t L hst hLs lambda x) atTop (𝓝 1) := by
 let : Nonempty (Fin s) := ⟨⟨0,hs⟩⟩
 have hc : Continuous (fun A : Matrix (Fin s) (Fin s) ℂ => A.det) := continuous_id.matrix_det
 have hd : Tendsto (fun x : ℝ => (theorem1PsiMatrix s t L hst hLs lambda x).det) atTop (𝓝 (0 : ℂ)) := by
   convert (hc.tendsto (0 : Matrix (Fin s) (Fin s) ℂ)).comp
     (theorem1PsiMatrix_tendsto_zero s t L hst hLs lambda) using 1 <;>
       first | rfl | simp only [Matrix.det_zero]
 have hn : Tendsto (fun x : ℝ => ‖(theorem1PsiMatrix s t L hst hLs lambda x).det‖)
     atTop (𝓝 (0 : ℝ)) := by simpa only [norm_zero] using hd.norm
 simpa only [theorem1CdfCandidate,zero_div,sub_zero] using
   (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).sub
     (hn.div_const ‖(theorem1PsiMatrix s t L hst hLs lambda 0).det‖)

theorem theorem2CdfCandidate_tendsto_one (s t L : ℕ) (hst : s ≤ t) (hLs : L ≤ s)
 (lambda : Fin L → ℝ) (hpos : ∀ j, 0 < lambda j) (hinj : Function.Injective lambda) :
 Tendsto (fun x : ℝ => theorem2CdfCandidate s t L hst hLs lambda x) atTop (𝓝 1) := by
 have hc : Continuous (fun A : Matrix (Fin s) (Fin s) ℂ => A.det) := continuous_id.matrix_det
 have hd := (hc.tendsto (theorem1PsiMatrix s t L hst hLs lambda 0)).comp
   (theorem2XiMatrix_tendsto_full s t L hst hLs lambda)
 have hden : ‖(theorem1PsiMatrix s t L hst hLs lambda 0).det‖ ≠ 0 :=
   norm_ne_zero_iff.mpr (theorem1PsiMatrix_zero_det_ne_zero s t L hst hLs lambda hpos hinj)
 simpa only [theorem2CdfCandidate,div_self hden, Function.comp_apply] using
   hd.norm.div_const ‖(theorem1PsiMatrix s t L hst hLs lambda 0).det‖

end
end JinWishart
#print axioms JinWishart.theorem1PsiMatrix_tendsto_zero
#print axioms JinWishart.theorem2XiMatrix_tendsto_full
#print axioms JinWishart.theorem1CdfCandidate_tendsto_one
#print axioms JinWishart.theorem2CdfCandidate_tendsto_one
