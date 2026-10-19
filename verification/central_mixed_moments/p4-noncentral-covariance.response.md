I'll review this Lean 4 formalization for concrete mathematical/logical issues only, focusing on the P4 criteria you specified.

## Concrete Issues Found

### 1. **Real vs Complex Scalar Mismatch in `noncentralSampleMinimum_amplitude_scale`**

The theorem states `(a : ℝ)` but coerces it to `ℂ` via `((a⁻¹ : ℝ) : ℂ)`. The issue: `complexNoncentralSampleSmallestEigenvalue` expects a complex matrix, and `a • z` where `a : ℝ` acts on `z : ComplexSample` (which is `Fin m → Fin n → ℂ`). The real scalar multiplication `a • z` multiplies each complex entry by `a` as a real number, which equals `(a : ℂ) • z`. However, the rescaled mean becomes `((a⁻¹ : ℝ) : ℂ) • M`, which is correct algebraically but **the physical interpretation requires `a > 0` to preserve the eigenvalue structure**. The hypothesis `ha : 0 < a` is present, so this is sound, but the coercion path `ℝ → ℂ` should be explicit about whether this models physical amplitude scaling (real) vs complex phase rotation.

**Verdict**: Mathematically correct given `ha : 0 < a`. No bug.

### 2. **`sqrt(v)` vs `v` Scaling — Potential Double-Square Issue**

In `actualNoncentralCovarianceMinimumCDF_eq`, you use:
```lean
simp only [..., noncentralSampleMinimum_amplitude_scale _ _ _ (Real.sqrt_pos.mpr hv), Real.sq_sqrt hv.le]
```

The noise is `Real.sqrt v • z`, so `a = Real.sqrt v` and `a^2 = v`. The rescaled mean is `((Real.sqrt v)⁻¹ : ℝ) : ℂ) • M = ((v^(-1/2)) : ℂ) • M`. Then:
- LHS: eigenvalue of `M + sqrt(v) * Z`
- RHS: `v * eigenvalue of (v^(-1/2) * M + Z)`

This gives `λ_min(M + √v Z) = v · λ_min(v^{-1/2} M + Z)`. **This is algebraically correct**: factoring out `√v` from the argument scales the minimum eigenvalue by `v = (√v)²`.

**Verdict**: Correct. The `Real.sq_sqrt hv.le` discharge is valid since `hv : 0 < v` implies `0 ≤ v`.

### 3. **Log-Ratio Cancellation at Zero — Reviewer Concern Addressed?**

In `tendsto_log_ratio_div_const`, the critical step:
```lean
have hlog : Real.log (x/v) ≠ 0 := (Real.log_neg (div_pos hx hv) ((div_lt_one hv).mpr hxv)).ne
```

This proves `log(x/v) < 0` eventually (when `x < v`), hence nonzero. The denominator `Real.log x` is also negative and nonzero for `x ∈ (0,1)`. The `field_simp` then cancels safely.

**However**, the earlier `hl` proof uses:
```lean
have hx0 : Real.log x ≠ 0 := (Real.log_neg hx hx1).ne
```
where `hx1` comes from `eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)`. This restricts to `x < 1` eventually, which is valid for `𝓝[>] 0`.

**Verdict**: The cancellation is justified. The reviewer's concern about "zero log at intermediate points" is handled by the `eventually` filters that exclude `x = 1` and `x = v` from the neighborhood. **No bug.**

### 4. **Physical Mean Fixed — Declaration Check**

You state: "Arbitrary FIXED M, noise sqrt(v)Z, v>0 fixed. This DOES NOT scale M together with noise."

In `actualNoncentralCovarianceMinimumCDF_eq`, the RHS uses `(((Real.sqrt v)⁻¹ : ℝ) : ℂ) • M`. For fixed `v`, this is a **fixed rescaling** of `M`, not a limit-dependent scaling. The diversity theorem then applies `actualNoncentralMinimumCDF_diversity` to this fixed rescaled matrix. Since diversity depends only on `d` (not on the specific matrix value, per your earlier theorems), the result `d+1` holds.

**Verdict**: Consistent with the physical model. The mean is fixed; the rescaling is a constant transformation for fixed `v`.

### 5. **High-SNR Threshold Diversity Sign**

```lean
Tendsto (fun r : ℝ => Real.log (actualNoncentralCovarianceMinimumCDF d n M v (b/r))/Real.log r)
  atTop (𝓝 (-((d+1 : ℕ) : ℝ)))
```

As `r → ∞`, `b/r → 0⁺`, so `CDF(b/r) ~ (b/r)^{d+1}` (from the low-x behavior). Thus:
- `log CDF(b/r) ~ (d+1) log(b/r) = (d+1)(log b - log r)`
- `log CDF / log r ~ (d+1)(log b / log r - 1) → -(d+1)`

**Verdict**: The sign `-((d+1))` is correct for high-SNR diversity.

### 6. **Missing Positivity Proof for `x/v` in `actualNoncentralCovarianceMinimumCDF_eq`**

The `rw [le_div_iff₀ hv]` step requires knowing the direction of inequality. Since `hv : 0 < v`, we have `v > 0`, so `x ≤ v · y ↔ x/v ≤ y`. But `le_div_iff₀` needs `0 < v`, which is `hv`. 

**However**, `le_div_iff₀` also requires the denominator to be nonzero, which `hv.ne'` provides. The `mul_comm` rewrite then gives `v * (x/v) = x`.

**Verdict**: Valid. No missing hypothesis.

---

## Summary of Findings

| Issue | Status |
|-------|--------|
| Real/complex scalar coercion | Sound (given `ha : 0 < a`) |
| `√v` vs `v` eigenvalue scaling | Algebraically correct |
| Log cancellation at zero | Properly handled by `eventually` filters |
| Fixed mean physical model | Consistent |
| High-SNR diversity sign | Correct (`-(d+1)`) |
| Division positivity side conditions | Discharged by `hv` |

**No concrete bugs found.** The formalization correctly implements the stated physics: fixed `M`, noise variance `v > 0` fixed, sample minimum equals `v` times standard-noise minimum with rescaled mean `M/√v`, and diversity `d+1` is preserved under constant positive rescaling.
