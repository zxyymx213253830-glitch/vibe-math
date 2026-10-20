# P4 Issues-Only Review

## Issue 1: Missing `classical` modifier

**File:** `CorrelatedGramTraceMoments.lean`, theorem `eval_correlatedGram_trace_sq` (line ~38)

The theorems `eval_correlatedGram_trace` and `eval_correlatedGram_squaredTrace` both open with `classical`, but `eval_correlatedGram_trace_sq` omits it. Since this theorem uses `MvPolynomial.eval` with `Sum.elim` on non-decidable index types, it likely requires `classical` for the same reasons as its siblings. This will either fail to compile or silently rely on ambient classical instances from upstream, creating fragility.

---

## Issue 2: Coercion mismatch `(m : ℝ)` vs `(m : ℂ)` in RHS type alignment

**File:** `CorrelatedGramTraceMoments.lean`, theorem `integral_actualCorrelatedGram_squaredTrace` (line ~79)

The algebraic moment (`complexGaussianMoment_correlatedGram_squaredTrace`) produces `(m : ℂ) * (complexGram B).trace ^ 2`. After taking real parts and using PSD imaginary-zero, the code writes `(m : ℝ) * (complexGram B).trace.re ^ 2`. This is arithmetically correct, but the coercion `(m : ℝ)` vs the algebra's `(m : ℂ)` means the simplifier must discharge `(m : ℂ).re = (m : ℝ)` implicitly through `norm_num`. If any upstream lemma changes coercion priorities, this `norm_num [Complex.add_re, Complex.mul_re, ...]` terminal step may stall. The same pattern appears in `integral_actualCorrelatedGram_trace_sq` and `integral_actualCorrelatedGram_trace_centered_sq`. This is not a bug today, but it couples proof stability to `norm_num`'s coercion normalization heuristics.

---

## Issue 3: `integral_add` / `integral_sub` integrability obligation ordering

**File:** `CorrelatedGramTraceMoments.lean`, theorem `integral_actualCorrelatedGram_trace_centered_sq` (line ~140)

```lean
have ha := integral_add (hi2.sub (hi.const_mul (2*T))) (integrable_const (T^2))
have hb := integral_sub hi2 (hi.const_mul (2*T))
```

Here `hb` proves integrability of the difference, but `ha` already uses `hi2.sub (hi.const_mul (2*T))` as an argument to `integral_add`. The term `hi2.sub (hi.const_mul (2*T))` constructs an `Integrable` proof object by calling `.sub` on `hi2`, which internally requires exactly what `hb` states. So `hb` is proved **after** being used. Lean accepts this because `hb` is a `have` (forward reference resolved at elaboration), but the logical dependency is: `ha` depends on the content of `hb`. If `.sub` ever changes its signature or requires explicit proof terms rather than typeclass inference, this will break. More importantly, `hb` is never actually used—`ha` already embeds the subtraction integrability. The line `rw [ha, hb, ...]` then rewrites with both, but `hb` rewrites a subexpression that `ha` already expanded, making the `rw` sequence order-dependent and redundant.

---

## Issue 4: No verification that `stdGaussian _` has total mass 1

**File:** `CorrelatedGramTraceMoments.lean`, theorem `integral_actualCorrelatedGram_trace_centered_sq` (line ~152)

```lean
simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
```

This discharges `∫ z, T^2 ∂stdGaussian _ = T^2` by asserting the measure of the universe is 1. This is valid **only if** `stdGaussian` on `ComplexSample (m := m) (n := p)` is a probability measure (total mass 1). The user prompt explicitly flags "Human measure/model review REQUIRED" and "centered integral subtraction mass1". The code assumes this without citing the relevant `IsProbabilityMeasure stdGaussian` instance or `volume_univ` lemma. If the Gaussian measure on the sample space is defined via product construction and the total-mass lemma is missing or conditional, this `simp` will fail. There is no `sorry` here, so either the instance exists upstream or this compiles only because of a coincidental `simp` set. **This is the highest-priority human-review item**: confirm `isProbabilityMeasure_stdGaussian` or equivalent is actually available for arbitrary finite index types.

---

## Issue 5: `correlatedGramSquaredTracePolynomial` sums over all `(i, j)` including diagonal

**File:** `CorrelatedGramTraceAlgebra.lean`, definition `correlatedGramSquaredTracePolynomial` (line ~16)

The polynomial `∑ i, ∑ j, G_ij * G_ji` correctly represents `trace(W^2)` since `(W^2)_{ii} = ∑_j W_{ij} W_{ji}`. No issue mathematically. However, when `i = j`, the term becomes `G_ii * G_ii = G_ii^2`, which is a degree-2 monomial in a single entry. The covariance formula `L(G_ij G_uv)` applied to `G_ii G_ii` yields `K_ii K_ii + m Σ_ii Σ_ii + Σ_ii A_ii + Σ_ii A_ii`. The algebra handles this correctly, but the Wick contraction for repeated indices (`i=j=u=v`) in the complex Gaussian model requires that `L(z_i \bar{z}_i z_i \bar{z}_i)` matches the fourth moment of a single CN(0,1) variable. The imported `complexGaussianMoment_correlatedGramEntry_product` must cover this diagonal case. If it was proved only for general position (distinct indices), the diagonal specialization may require additional justification. The user prompt states the imports are "PROVED" for general Gram product, so this is a verification checkpoint rather than a known error.

---

## Summary

| # | Severity | Type | Location |
|---|----------|------|----------|
| 1 | Low | Missing `classical` | `CorrelatedGramTraceMoments.lean`, `eval_correlatedGram_trace_sq` |
| 2 | Low | Coercion fragility | `integral_actualCorrelatedGram_squaredTrace`, `_trace_sq`, `_centered_sq` |
| 3 | Low | Redundant/unused `have` | `integral_actualCorrelatedGram_trace_centered_sq` line 140 |
| 4 | **Medium** | Probability mass assumption unverified | `integral_actualCorrelatedGram_trace_centered_sq` line 152 |
| 5 | Low | Diagonal Wick case reliance | `correlatedGramSquaredTracePolynomial` evaluation |

No algebraic sign errors, trace/square-trace confusion, or index-finiteness issues detected. The core formulas match the user-stated targets.
