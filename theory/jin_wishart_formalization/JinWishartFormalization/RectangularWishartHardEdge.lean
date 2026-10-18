import JinWishartFormalization.RectangularWishartOneExtraRow
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Data.Nat.Choose.Cast

/-! Central (n+1)-by-n actual minimum: hard-edge exponent two.
Codex proof bodies. [需人工审查] Interpretation as an actual spectral CDF.
The probability law is imported, not assumed as a premise.
-/
open Filter MeasureTheory ProbabilityTheory Set Topology
namespace JinWishart
noncomputable section

private def p1 (n : ℕ) (x : ℝ) : ℝ :=
  ∑ l ∈ Finset.range (n+1), (n.choose l : ℝ) / (l.factorial : ℝ) * l * x^(l-1)
private def p2 (n : ℕ) (x : ℝ) : ℝ :=
  ∑ l ∈ Finset.range (n+1), (n.choose l : ℝ) / (l.factorial : ℝ) * l * (l-1 : ℕ) * x^(l-2)

private theorem dP (n : ℕ) (x : ℝ) :
    HasDerivAt (oneExtraRowMinimumPolynomial n) (p1 n x) x := by
  unfold oneExtraRowMinimumPolynomial p1
  convert HasDerivAt.fun_sum (fun l (_ : l ∈ Finset.range (n+1)) =>
    ((hasDerivAt_pow l x).const_mul ((n.choose l : ℝ) / (l.factorial : ℝ)))) using 1 <;>
    simp only [mul_div_assoc, div_mul_eq_mul_div, mul_assoc]

private theorem dP1 (n : ℕ) (x : ℝ) : HasDerivAt (p1 n) (p2 n x) x := by
  unfold p1 p2
  convert HasDerivAt.fun_sum (fun l (_ : l ∈ Finset.range (n+1)) =>
    ((hasDerivAt_pow (l-1) x).const_mul ((n.choose l : ℝ) / (l.factorial : ℝ) * l))) using 1 <;>
    simp only [Nat.sub_sub, one_add_one_eq_two, mul_assoc]

private theorem P0 (n : ℕ) : oneExtraRowMinimumPolynomial n 0 = 1 := by
  unfold oneExtraRowMinimumPolynomial
  rw [Finset.sum_eq_single 0]
  · simp
  · intro l hl hne
    simp [zero_pow hne]
  · simp

private theorem P10 (n : ℕ) (hn : 0 < n) : p1 n 0 = n := by
  unfold p1
  rw [Finset.sum_eq_single 1]
  · simp
  · intro l hl hne
    by_cases h0 : l = 0
    · simp [h0]
    · have hp : l-1 ≠ 0 := by omega
      simp [zero_pow hp]
  · intro h
    have : 1 ∈ Finset.range (n+1) := Finset.mem_range.mpr (by omega)
    exact (h this).elim

private theorem P20 (n : ℕ) : p2 n 0 = (n.choose 2 : ℝ) := by
  unfold p2
  rw [Finset.sum_eq_single 2]
  · norm_num
  · intro l hl hne
    by_cases h0 : l = 0
    · simp [h0]
    by_cases h1 : l = 1
    · simp [h1]
    have hp : l-2 ≠ 0 := by omega
    simp [zero_pow hp]
  · intro h
    have hn : n < 2 := by simpa using h
    simp [Nat.choose_eq_zero_of_lt hn]

/-- The analytic CDF expression has quadratic leading coefficient n(n+1)/4. -/
theorem oneExtraRowMinimumCDF_div_square_tendsto (n : ℕ) (hn : 0 < n) :
    Tendsto (fun x : ℝ =>
      (1-Real.exp (-(n : ℝ)*x)*oneExtraRowMinimumPolynomial n x)/x^2)
      (𝓝[>] 0) (𝓝 ((n : ℝ)*(n+1)/4)) := by
  let f := fun x : ℝ => 1-Real.exp (-(n : ℝ)*x)*oneExtraRowMinimumPolynomial n x
  let g := fun x : ℝ => Real.exp (-(n : ℝ)*x)*
    ((n : ℝ)*oneExtraRowMinimumPolynomial n x-p1 n x)
  have he (x : ℝ) : HasDerivAt (fun y : ℝ => Real.exp (-(n : ℝ)*y))
      (-(n : ℝ)*Real.exp (-(n : ℝ)*x)) x := by
    convert ((hasDerivAt_id x).const_mul (-(n : ℝ))).exp using 1 <;> simp [id_eq] <;> ring
  have hf (x : ℝ) : HasDerivAt f (g x) x := by
    convert ((he x).mul (dP n x)).const_sub 1 using 1 <;> dsimp [f,g] <;> ring
  have hg0 : g 0 = 0 := by simp [g, P0, P10 n hn]
  have hdg : HasDerivAt g ((n : ℝ)^2-(n.choose 2 : ℝ)) 0 := by
    convert (he 0).mul (((dP n 0).const_mul (n : ℝ)).sub (dP1 n 0)) using 1 <;>
      simp [g, Pi.sub_apply, P0, P10 n hn, P20] <;> ring
  have hlim : Tendsto (fun x : ℝ => g x / (2*x)) (𝓝[>] 0)
      (𝓝 ((n : ℝ)*(n+1)/4)) := by
    have h := hdg.tendsto_slope_zero_right.div_const 2
    convert h using 1
    · ext x
      simp only [smul_eq_mul, zero_add, hg0, sub_zero]
      ring
    · rw [Nat.cast_choose_two]
      ring
  apply HasDerivAt.lhopital_zero_nhdsGT (f' := g) (g' := fun x : ℝ => 2*x)
  · exact Filter.Eventually.of_forall hf
  · filter_upwards [] with x
    convert hasDerivAt_pow 2 x using 1 <;> norm_num
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact ne_of_gt (mul_pos (by norm_num) hx)
  · have h : Tendsto f (𝓝[>] 0) (𝓝 (f 0)) :=
      (hf 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa [f, P0] using h
  · have h : Tendsto (fun x : ℝ => x^2) (𝓝[>] 0) (𝓝 ((0 : ℝ)^2)) :=
      ((continuous_pow 2).tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using h
  · exact hlim

/-- Actual central rectangular minimum, arbitrary positive column count. -/
theorem actualOneExtraRow_minimum_hardEdge (n : ℕ) (hn : 0 < n) :
    Tendsto (fun x : ℝ => cdf
      ((stdGaussian (ComplexSample (m := n+1) (n := n))).map
        (oneExtraRowSampleMinimum n hn)) x / x^2)
      (𝓝[>] 0) (𝓝 ((n : ℝ)*(n+1)/4)) := by
  apply (oneExtraRowMinimumCDF_div_square_tendsto n hn).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [actualOneExtraRow_minimum_cdf_function, if_pos (le_of_lt hx)]

/-- Scalar covariance vI changes the coefficient by v^(-2), not v^(-1). -/
theorem actualOneExtraRow_covariance_minimum_hardEdge (n : ℕ) (hn : 0 < n)
    (v : ℝ) (hv : 0 < v) :
    Tendsto (fun x : ℝ =>
      ((stdGaussian (ComplexSample (m := n+1) (n := n)))
        {z | oneExtraRowSampleMinimum n hn (Real.sqrt v • z) ≤ x}).toReal / x^2)
      (𝓝[>] 0) (𝓝 ((n : ℝ)*(n+1)/(4*v^2))) := by
  have hz : Tendsto (fun x : ℝ => x/v) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun x : ℝ => x/v) (𝓝[>] 0) (𝓝 (0/v)) :=
      ((continuous_id.div_const v).tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using h
  have hp : ∀ᶠ x : ℝ in 𝓝[>] 0, x/v ∈ Ioi (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact div_pos hx hv
  have hs := tendsto_nhdsWithin_iff.mpr ⟨hz,hp⟩
  have h := ((oneExtraRowMinimumCDF_div_square_tendsto n hn).comp hs).div_const (v^2)
  have hr : Tendsto (fun x : ℝ =>
      ((stdGaussian (ComplexSample (m := n+1) (n := n)))
        {z | oneExtraRowSampleMinimum n hn (Real.sqrt v • z) ≤ x}).toReal / x^2)
      (𝓝[>] 0) (𝓝 ((n : ℝ)*(n+1)/4 / v^2)) := by
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [actualOneExtraRow_covariance_minimum_CDF n hn v hv x (le_of_lt hx)]
    dsimp [Function.comp_def]
    have hxpos : (0 : ℝ) < x := hx
    field_simp [ne_of_gt hv, ne_of_gt hxpos]
  convert hr using 1 <;> ring

end
end JinWishart
#print axioms JinWishart.oneExtraRowMinimumCDF_div_square_tendsto
#print axioms JinWishart.actualOneExtraRow_minimum_hardEdge
#print axioms JinWishart.actualOneExtraRow_covariance_minimum_hardEdge
