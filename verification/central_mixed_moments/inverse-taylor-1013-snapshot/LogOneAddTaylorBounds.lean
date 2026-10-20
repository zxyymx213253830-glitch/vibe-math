import JinWishartFormalization.LogDetLowScaleSecondOrder
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Global positive-side Taylor inequalities for log(1+u), not a power-series assumption.
Codex deterministic calculus, controls precede formalization.
-/
open Set
namespace JinWishart
noncomputable section

private theorem nonneg_of_nonneg_derivative_on_nonneg (f g : ℝ → ℝ)
    (hf0 : f 0=0) (hd : ∀ x, 0≤x → HasDerivAt f (g x) x)
    (hg : ∀ x, 0≤x → 0≤g x) (u : ℝ) (hu : 0≤u) : 0≤f u := by
  have hc : ContinuousOn f (Ici 0) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hmono : MonotoneOn f (Ici 0) := monotoneOn_of_hasDerivWithinAt_nonneg
    (convex_Ici 0) hc (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
    (fun x hx => hg x (interior_subset hx))
  simpa only [hf0] using hmono (show (0:ℝ)∈Ici 0 by simp) hu hu

theorem log_one_add_quadratic_gap_bounds (u : ℝ) (hu : 0≤u) :
    0≤u-Real.log (1+u) ∧ u-Real.log (1+u)≤u^2/2 := by
  have hd (x : ℝ) (hx : 0≤x) :
      HasDerivAt (fun t : ℝ => Real.log (1+t)-t+t^2/2) (x^2/(1+x)) x := by
    have hp : 0<1+x := by positivity
    have h := ((((hasDerivAt_id x).const_add 1).log hp.ne').sub (hasDerivAt_id x)).add
      (((hasDerivAt_id x).fun_pow 2).div_const 2)
    convert h using 1
    · rfl
    · dsimp
      field_simp [hp.ne']
      <;> ring
  have h := nonneg_of_nonneg_derivative_on_nonneg
    (fun t => Real.log (1+t)-t+t^2/2) (fun x => x^2/(1+x))
    (by norm_num) hd (fun x hx => by positivity) u hu
  exact ⟨(log_one_add_linear_gap_bounds u hu).1,by linarith⟩

theorem log_one_add_cubic_remainder_bounds (u : ℝ) (hu : 0≤u) :
    0≤Real.log (1+u)-u+u^2/2 ∧ Real.log (1+u)-u+u^2/2≤u^3/3 := by
  have hd (x : ℝ) (hx : 0≤x) :
      HasDerivAt (fun t : ℝ => t^3/3-Real.log (1+t)+t-t^2/2) (x^3/(1+x)) x := by
    have hp : 0<1+x := by positivity
    have h := (((((hasDerivAt_id x).fun_pow 3).div_const 3).sub
      (((hasDerivAt_id x).const_add 1).log hp.ne')).add (hasDerivAt_id x)).sub
      (((hasDerivAt_id x).fun_pow 2).div_const 2)
    convert h using 1
    · rfl
    · dsimp
      field_simp [hp.ne']
      <;> ring
  have h := nonneg_of_nonneg_derivative_on_nonneg
    (fun t => t^3/3-Real.log (1+t)+t-t^2/2) (fun x => x^3/(1+x))
    (by norm_num) hd (fun x hx => by positivity) u hu
  exact ⟨by have := (log_one_add_quadratic_gap_bounds u hu).2; linarith,by linarith⟩

end
end JinWishart
#print axioms JinWishart.log_one_add_quadratic_gap_bounds
#print axioms JinWishart.log_one_add_cubic_remainder_bounds
