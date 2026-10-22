# P4 Adversarial Review

## FiniteSpectrumOffsetL2.lean

**1. Missing `r ≥ 1` condition in pointwise tendsto proof.**
In `positiveModeOffsetError_tendsto`, the filter `eventually_gt_atTop (0:ℝ)` only guarantees `r > 0`. However, `positiveModeOffsetError_nonneg_le` requires `hr : 1 ≤ r`. The pointwise convergence proof unfolds the definition and uses `Real.log_mul hr.ne' harg.ne'` where `hr : 0 < r` suffices algebraically, but the dominated convergence application in the integral theorem filters on `eventually_ge_atTop (1:ℝ)`. This is not a gap—the integral proof correctly restricts to `r ≥ 1`—but the pointwise result is stated unconditionally while only being applied under `r ≥ 1`. No mathematical error; just imprecise documentation of where the bound matters.

**2. Potential issue: `Real.log r` measurability branch.**
In `hmeas`, the term `(hiM.mul_const (Real.log r))` treats `Real.log r` as a constant, which is valid for fixed `r`. However, when `r ≤ 0`, `Real.log r = 0` by Lean's totalized definition. The proof restricts to `r ≥ 1` via `eventually_ge_atTop`, so this is never exercised. Not a gap.

**3. Actual gap: `sq_abs` usage without verification.**
The line `nlinarith only [hp,sq_abs (positiveSpectrumLog (f i a)),sq_nonneg (f i a-|positiveSpectrumLog (f i a)|)]` invokes `sq_abs`. This is mathlib-standard and correct. No issue.

**4. Domination bound correctness.**
The bound `(x + |positiveSpectrumLog x|)^2 ≤ 2*x^2 + 2*(positiveSpectrumLog x)^2` follows from `(a+b)^2 ≤ 2a^2 + 2b^2`. The proof uses `pow_le_pow_left₀ he.1 he.2 2` then `nlinarith`. This is valid. No gap.

## ActualSingularOffsetL2.lean

**5. Rank coercion gap.**
```lean
have hR : ((complexSampleMatrix z*B+M).rank : ℝ)=R := by
  rw [hz,← matrix_fromRows_rank_eq]
```
Here `R := (min m (Matrix.fromRows B M).rank : ℕ)` is defined as a natural number coerced to `ℝ`. The hypothesis `hz` from `actualCorrelatedRank_eq_generic_ae B M` should provide AE equality of ranks. **However**, the proof writes `rw [hz, ← matrix_fromRows_rank_eq]` where `hz` is an AE statement being used inside a `filter_upwards` block. This is correct—`hz` here is the pointwise specialization at `z`. No gap, provided `actualCorrelatedRank_eq_generic_ae` yields the correct pointwise rank equality (which it must, as a separately checked dependency).

**6. Critical gap: `hcount` type mismatch.**
```lean
have hc := gram_positive_modes_eq_rank (complexSampleMatrix z*B+M)
change (∑ i,if 0<actualCorrelatedEigenvalue B M i z then (1:ℝ) else 0)=_ at hc
have hR : ((complexSampleMatrix z*B+M).rank : ℝ)=R := ...
have hcount := hc.trans hR
```
The `change` tactic asserts that the sum of indicator functions equals something, but `hc` originally equates a **natural number** count to a rank. After `change`, the LHS becomes a real-valued sum. The transitivity `hc.trans hR` requires both sides to be reals. If `gram_positive_modes_eq_rank` returns a `ℕ`-equality and the `change` forces a coercion, this works only if the coercion is definitionally transparent. **This is a potential gap**: verify that `gram_positive_modes_eq_rank` produces an equality in `ℝ` after the `change`, or that the coercion commutes with the sum-of-indicators representation.

**7. Spectral identity assumption.**
The proof uses `actualCorrelatedMatrixLogDet_eq_spectral` to equate the logdet with the eigenvalue sum. This is imported and treated as a checked dependency. No issue unless its signature mismatches the call site (it doesn't appear to).

**Summary:** One substantive concern—item **6** (the `change`/coherence step in `hcount`) warrants manual verification that the numeric-to-real coercion aligns definitionally with the indicator sum. Everything else is either correct or a non-issue under the stated filter restrictions.
