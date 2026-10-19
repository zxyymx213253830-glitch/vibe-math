# P4 Concrete Issue Audit: LogDetLowScaleSecondOrder & ActualLogDetLowScaleCurvature

I need to carefully audit these files for concrete mathematical issues, targeting all finite m,n including 0, arbitrary fixed complex mean M, with no full-rank assumptions. Let me examine the key components.

## Critical Issues Found

### 1. **Division by Zero in `integral_log_one_add_second_order` Rewrite**

In `LogDetLowScaleSecondOrder.lean`, the final rewrite step:

```lean
rw [integral_div] at ht
```

This is problematic. While you correctly note that `integral_div` has no L1 premise in mathlib, the issue is that this rewrite produces `(∫ a, (f a)^2 ∂μ) / r^2` when applied to the integrand divided by `r^2`. But `r` is approaching 0 from the right (in `𝓝[>] 0`), and you're rewriting **before** taking the limit. The expression `(r*(∫ f) - ∫ log(1+r*f))/r^2` should remain as a single fraction for `r > 0`. The `integral_div` rewrite is valid for each fixed `r > 0`, but the way it's used here creates a term-by-term division that obscures the cancellation structure needed for the limit.

**Concrete fix**: Keep the combined fraction structure until after establishing the pointwise limit, then use linearity of integration.

### 2. **Missing Empty Index Set Case (`n = 0`)**

In `integral_finiteSpectrumLogDet_second_order`, when `ι` is empty (corresponding to `n = 0` matrices):
- `finiteSpectrumLogDet` over an empty index set should equal 0
- The sum `∑ i, ...` over empty `Finset.univ` equals 0
- You get `Tendsto (fun r => (r*0 - 0)/r^2) (𝓝[>] 0) (𝓝 0)` which is `Tendsto (fun r => 0) ...` — this works, but only if `finiteSpectrumLogDet` is properly defined for empty spectra.

**Verify**: Does your `finiteSpectrumLogDet` definition handle `Fintype.card ι = 0`? If it's defined as `∑ i, Real.log (1 + r * f i)`, then empty sum = 0 is fine.

### 3. **Factor of 1/2 Accounting in Curvature Theorem**

In `ActualLogDetLowScaleCurvature.lean`, the target limit is:
```lean
(∑ i, ∫ z, (complexNoncentralSampleEigenvalue M i z)^2 ∂stdGaussian _) / 2
```

But tracing through from `integral_finiteSpectrumLogDet_second_order`, you get:
```lean
(∑ i, ∫ a, (f i a)^2 ∂μ) / 2
```

The factor of 1/2 comes from the scalar limit `(x*r - log(1+x*r))/r^2 → x^2/2`. This is correct via L'Hôpital. However, verify that `actualExpectedGramPower_eq_closed` doesn't introduce additional factors. The trace formula `T = m*n + ∑‖M_ij‖^2` should appear without extra 1/2 factors in the linear term.

### 4. **L4 Integrability Chain for Eigenvalues**

In `integrable_actualNoncentralEigenvalue_sq`:
```lean
have hi := (hid.add hc).integrable_norm_pow' (p := 4)
```

You're using that `‖z + M‖^4` is integrable to bound eigenvalue squares. The domination:
```lean
(complexNoncentralSampleEigenvalue M i z)^2 ≤ ‖z + complexSampleMean M‖^4 / 4
```

This relies on `λ_i ≤ trace` and `trace = ‖·‖^2 / 2`, giving `λ_i^2 ≤ trace^2 = ‖·‖^4 / 4`. This is **correct** for nonneg eigenvalues bounded by trace. No rank assumption needed — zero eigenvalues contribute 0 ≤ RHS. ✓

### 5. **Measurability Side Conditions in DCT Application**

In `integral_log_one_add_second_order`, the domination proof uses:
```lean
have hrp : 0 < r := hr
filter_upwards [hn] with a ha
obtain ⟨h0,h1⟩ := log_one_add_linear_gap_bounds (r*f a) (mul_nonneg hrp.le ha)
```

The bound `(r*f a - log(1+r*f a))/r^2 ≤ (r*f a)^2/r^2 = (f a)^2` is correct. But you need `(f a)^2` integrable — that's exactly `hf2`. ✓

However, the measurability argument:
```lean
((hf.aemeasurable.const_mul r).sub (Real.measurable_log.comp_aemeasurable ...))
```

For `r > 0` fixed, `1 + r*f a > 0` a.e. (since `f ≥ 0` a.e.), so `log(1+r*f)` is measurable. ✓

### 6. **L'Hôpital Derivative Quotient Simplification**

In `log_one_add_second_order_limit`, the derivative quotient is:
```lean
(x - x/(1+r*x)) / (2*r)
```

Algebraic simplification:
```
x - x/(1+r*x) = x*(1+r*x)/(1+r*x) - x/(1+r*x) = x*r*x/(1+r*x) = r*x^2/(1+r*x)
```

So the quotient becomes `r*x^2 / ((1+r*x) * 2*r) = x^2 / (2*(1+r*x)) → x^2/2` as `r → 0⁺`. ✓

The code shows this via `field_simp; ring` — correct.

### 7. **Scalar Function at x = 0**

For `x = 0`: `(r*0 - log(1+0))/r^2 = 0/r^2 = 0` for all `r > 0`, limit is `0 = 0^2/2`. ✓  
Real division is total at 0 in Lean (returns 0), so no domain issue.

## Summary of Concrete Actions Needed

| # | Issue | Severity | Action |
|---|-------|----------|--------|
| 1 | `integral_div` rewrite timing | Medium | Verify the rewrite preserves the limit structure; consider deferring division expansion |
| 2 | Empty spectrum `n=0` | Low | Confirm `finiteSpectrumLogDet` handles empty sums (likely already OK) |
| 3 | Factor 1/2 consistency | Low | Trace through `actualExpectedGramPower_eq_closed` to confirm no double-counting |
| 4 | L4 domination chain | None | Correct as-is |
| 5 | Measurability for DCT | None | Correct as-is |
| 6 | L'Hôpital algebra | None | Correct as-is |
| 7 | x=0 edge case | None | Handled by totality of real division |

## Axiom Compliance

All four `#print axioms` should show only `standard3axioms` (classical choice, propext, funext) or `actualexit0` markers. No `sorry` or additional axioms expected from these proofs.

## Human Review Checklist (P4 Requirements)

- [ ] **Measure-theoretic**: Fubini/Tonelli not invoked implicitly; finite sum exchange is explicit ✓
- [ ] **Variance/curvature interpretation**: Second spectral moment is empirical, not assumed closed-form ✓
- [ ] **Model alignment**: `complexNoncentralSampleEigenvalue` paired/sqrt2 source matches `ActualGaussianTraceMean` ✓
- [ ] **Boundary cases**: m=0 or n=0 produce empty sums, limits degenerate to 0=0 ✓
- [ ] **No rank/density assumptions**: Zero eigenvalues allowed throughout ✓

The files are structurally sound for P4. The primary verification burden is confirming that `integral_div` manipulation in the presence of the `r → 0⁺` filter doesn't create a spurious 0/0 form before the limit is taken — but since you work in `𝓝[>] 0` where `r > 0`, division by `r^2` is legitimate at every stage.
