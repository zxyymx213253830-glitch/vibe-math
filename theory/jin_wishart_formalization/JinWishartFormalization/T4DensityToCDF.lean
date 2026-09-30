import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Density hard-edge asymptotics imply CDF hard-edge asymptotics

This is a measure-theoretic/analytic bridge only. It does not identify a
Wishart eigenvalue density; a separate theorem must supply that density and
the local factorization hypotheses below.
-/

open Filter MeasureTheory Set Topology

namespace JinWishart

noncomputable section

/-- A local right-limit condition, stated in epsilon-delta form to make the
one-sided domain explicit. -/
def HasRightLimit (g : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ y, 0 < y → y < δ → |g y - a| < ε

private theorem powerIntegral_unit (d : ℕ) :
    (∫ s in (0 : ℝ)..1, s ^ d) = (d + 1 : ℝ)⁻¹ := by
  rw [integral_pow]
  field_simp
  norm_num

private theorem densityIntegral_rescale (d : ℕ) (g : ℝ → ℝ) (x : ℝ) :
    (∫ u in (0 : ℝ)..x, u ^ d * g u) =
      x ^ (d + 1) * ∫ s in (0 : ℝ)..1, s ^ d * g (s * x) := by
  have hscale := intervalIntegral.smul_integral_comp_mul_right
    (fun u : ℝ => u ^ d * g u) x (a := (0 : ℝ)) (b := 1)
  have hfactor : (∫ s in (0 : ℝ)..1, (s * x) ^ d * g (s * x)) =
      x ^ d * ∫ s in (0 : ℝ)..1, s ^ d * g (s * x) := by
    calc
      _ = ∫ s in (0 : ℝ)..1, x ^ d * (s ^ d * g (s * x)) := by
        apply intervalIntegral.integral_congr
        intro s _
        change (s * x) ^ d * g (s * x) = _
        rw [mul_pow]
        ring
      _ = _ := intervalIntegral.integral_const_mul ..
  calc
    _ = x * ∫ s in (0 : ℝ)..1, (s * x) ^ d * g (s * x) := by
      simpa [smul_eq_mul] using hscale.symm
    _ = x ^ (d + 1) * ∫ s in (0 : ℝ)..1, s ^ d * g (s * x) := by
      rw [hfactor, pow_succ]
      ring

private theorem scaledDensityIntegral_tendsto
    (d : ℕ) (a : ℝ) (g : ℝ → ℝ)
    (hlocal : HasRightLimit g a)
    (hint : ∀ x, 0 < x → IntervalIntegrable
      (fun u : ℝ => u ^ d * g u) volume 0 x) :
    Tendsto (fun x : ℝ => ∫ s in (0 : ℝ)..1, s ^ d * g (s * x))
      (𝓝[>] 0) (𝓝 (a / (d + 1 : ℝ))) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η : ℝ := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨δ, hδ, hlocalδ⟩ := hlocal η hη
  have hsmall : ∀ᶠ x : ℝ in 𝓝[>] 0, dist x 0 < min δ 1 := by
    have hball : ∀ᶠ x : ℝ in 𝓝 0, dist x 0 < min δ 1 :=
      Metric.eventually_nhds_iff.mpr ⟨min δ 1,
        lt_min hδ (by norm_num), fun x hx => hx⟩
    exact hball.filter_mono inf_le_left
  filter_upwards
      [hsmall, self_mem_nhdsWithin] with x hxδ hxpos
  have hxpos' : 0 < x := hxpos
  have hxδ' : x < min δ 1 := by
    have hxabs : |x| < min δ 1 := by simpa [Real.dist_eq] using hxδ
    exact (abs_lt.mp hxabs).2
  have hxsmall : x < δ := lt_of_lt_of_le hxδ' (min_le_left _ _)
  have hfx : IntervalIntegrable (fun u : ℝ => u ^ d * g u) volume 0 x :=
    hint x hxpos
  have hcomp : IntervalIntegrable
      (fun s : ℝ => (s * x) ^ d * g (s * x)) volume 0 1 := by
    have h := hfx.comp_mul_right (c := x)
    simpa [hxpos'.ne'] using h
  have hcomp' : IntervalIntegrable
      (fun s : ℝ => x ^ d * (s ^ d * g (s * x))) volume 0 1 := by
    convert hcomp using 1
    funext s
    rw [mul_pow]
    ring
  have hq : IntervalIntegrable
      (fun s : ℝ => s ^ d * g (s * x)) volume 0 1 := by
    have hxd : x ^ d ≠ 0 := pow_ne_zero _ hxpos.ne'
    have h := hcomp'.div_const (x ^ d)
    convert h using 1
    funext s
    field_simp [hxd]
  have hconst : IntervalIntegrable (fun s : ℝ => s ^ d * a) volume 0 1 :=
    (continuousOn_id.pow d).mul_const a |>.intervalIntegrable
  have hdiffInt : IntervalIntegrable
      (fun s : ℝ => s ^ d * g (s * x) - s ^ d * a) volume 0 1 :=
    hq.sub hconst
  have hbound : ∀ s ∈ uIoc (0 : ℝ) 1,
      ‖s ^ d * g (s * x) - s ^ d * a‖ ≤ η := by
    intro s hs
    have hsIcc : s ∈ Icc (0 : ℝ) 1 := by
      have hs' : s ∈ Ioc (0 : ℝ) 1 := by
        simpa [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs
      exact Ioc_subset_Icc_self hs'
    by_cases hs0 : s = 0
    · subst s
      simp at hs
    · have hspos : 0 < s := lt_of_le_of_ne hsIcc.1 (Ne.symm hs0)
      have hsxpos : 0 < s * x := mul_pos hspos hxpos
      have hsxsmall : s * x < δ := by
        calc
          s * x ≤ 1 * x := mul_le_mul_of_nonneg_right hsIcc.2 (le_of_lt hxpos')
          _ = x := one_mul x
          _ < δ := hxsmall
      have hnear := hlocalδ (s * x) hsxpos hsxsmall
      have hsPow0 : 0 ≤ s ^ d := pow_nonneg hsIcc.1 _
      have hsPow1 : s ^ d ≤ 1 := pow_le_one₀ hsIcc.1 hsIcc.2
      rw [show s ^ d * g (s * x) - s ^ d * a =
        s ^ d * (g (s * x) - a) by ring, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg hsPow0]
      have hstrict : s ^ d * |g (s * x) - a| < η := by
        calc
          s ^ d * |g (s * x) - a| ≤ 1 * |g (s * x) - a| :=
            mul_le_mul_of_nonneg_right hsPow1 (abs_nonneg _)
          _ = |g (s * x) - a| := one_mul _
          _ < η := hnear
      exact le_of_lt hstrict
  have herr : ‖∫ s in (0 : ℝ)..1,
      (s ^ d * g (s * x) - s ^ d * a)‖ ≤ η := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    simpa using h
  have hsub : (∫ s in (0 : ℝ)..1, s ^ d * g (s * x)) -
      ∫ s in (0 : ℝ)..1, s ^ d * a =
      ∫ s in (0 : ℝ)..1, (s ^ d * g (s * x) - s ^ d * a) := by
    rw [intervalIntegral.integral_sub hq hconst]
  have hpow : (∫ s in (0 : ℝ)..1, s ^ d * a) =
      (d + 1 : ℝ)⁻¹ * a := by
    rw [intervalIntegral.integral_mul_const, powerIntegral_unit]
  have herr' : ‖(∫ s in (0 : ℝ)..1, s ^ d * g (s * x)) -
      a / (d + 1 : ℝ)‖ ≤ η := by
    have hh := herr
    rw [← hsub, hpow] at hh
    simpa [div_eq_mul_inv, mul_comm] using hh
  have hdist : dist (∫ s in (0 : ℝ)..1, s ^ d * g (s * x))
      (a / (d + 1 : ℝ)) ≤ η := by
    simpa [Real.dist_eq, Real.norm_eq_abs, abs_sub_comm] using herr'
  have hηlt : η < ε := by dsimp [η]; nlinarith [hε]
  rw [Real.dist_eq]
  exact lt_of_le_of_lt hdist hηlt

/-- If a density has the local form `f(u)=u^d g(u)`, and its normalized
factor `g` has right limit `a`, then integrating the density raises the hard-
edge exponent by one and divides the coefficient by `d+1`.

`hint` explicitly supplies local interval integrability of the density. No
continuity assumption is made on `g`; endpoint values do not affect the integral.
-/
theorem density_to_cdf_hardEdge
    (d : ℕ) (a : ℝ) (g : ℝ → ℝ)
    (hlocal : HasRightLimit g a)
    (hint : ∀ x, 0 < x → IntervalIntegrable
      (fun u : ℝ => u ^ d * g u) volume 0 x) :
    Tendsto (fun x : ℝ =>
      (∫ u in (0 : ℝ)..x, u ^ d * g u) / x ^ (d + 1))
      (𝓝[>] 0) (𝓝 (a / (d + 1 : ℝ))) := by
  have hJ := scaledDensityIntegral_tendsto d a g hlocal hint
  have hEq : (fun x : ℝ =>
      (∫ u in (0 : ℝ)..x, u ^ d * g u) / x ^ (d + 1)) =ᶠ[𝓝[>] 0]
      (fun x : ℝ => ∫ s in (0 : ℝ)..1, s ^ d * g (s * x)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxpos : 0 < x := hx
    have hscale := densityIntegral_rescale d g x
    calc
      (∫ u in (0 : ℝ)..x, u ^ d * g u) / x ^ (d + 1) =
          (x ^ (d + 1) * ∫ s in (0 : ℝ)..1, s ^ d * g (s * x)) /
            x ^ (d + 1) := by rw [hscale]
      _ = ∫ s in (0 : ℝ)..1, s ^ d * g (s * x) := by
        field_simp [pow_ne_zero _ hxpos.ne']
        apply intervalIntegral.integral_congr
        intro s hs
        change s ^ d * g (s * x) = s ^ d * g (x * s)
        rw [mul_comm s x]
  exact hJ.congr' hEq.symm

end

end JinWishart
