# P4 Review: NoncentralMinimumComparison & NoncentralMinimumDiversity

## 1. Measure.real and ofReal interaction (Critical)

In `stdGaussian_shift_real_event_bounds`, the conversion from ENNReal to Real needs scrutiny:

```lean
have hlR := ENNReal.toReal_mono (by finiteness) hl
```

The `by finiteness` placeholder must actually resolve to a proof that `(stdGaussian _).real S ≠ ⊤`. Since `stdGaussian` is a probability measure, its total mass is 1, but `.real` extracts the underlying real-valued measure. The finiteness tactic needs to confirm the measure of the specific preimage set is finite. If `finiteness` succeeds silently without discharging the actual goal state, this is an axiom hole. Verify with `#check` or explicit `measure_ne_top`.

Similarly for `huR`:
```lean
have huR := ENNReal.toReal_mono (by
  rw [Measure.smul_apply,smul_eq_mul]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hu
```
This direction is better — it explicitly handles the scalar multiplication. But ensure `ENNReal.ofReal_ne_top` applies correctly when the constant `gaussianShiftUpperConstant y` could be zero (it can't, since it's `2^D * exp(h)` with both factors positive, but Lean needs to see this).

## 2. Preimage variance scaling signs

The sandwich uses:
- Lower: `(fun z => (1/2 : ℝ) • z) ⁻¹' S` → variance 1/4
- Upper: `(fun z => (2 : ℝ) • z) ⁻¹' S` → variance 4

Check directionality carefully. If `Z ~ N(0,I)`, then `Z/2 ~ N(0, I/4)` and `2Z ~ N(0, 4I)`. The imported Gaussian shift theorem states:

$$2^{-D} e^{-h} \text{Law}(Z/2) \leq \text{Law}(Z+\mu) \leq 2^D e^{h} \text{Law}(2Z)$$

So the **lower** bound on the shifted measure uses the **smaller-variance** central law (variance 1/4), and the **upper** bound uses the **larger-variance** central law (variance 4). This matches your code. ✓

## 3. complexSampleMean additivity

```lean
theorem centralGaussianSampleMinimum_shift {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (hn : 0 < n) (z : ComplexSample (m := m) (n := n)) :
    centralGaussianSampleMinimum m n hn (z+complexSampleMean M) =
      complexNoncentralSampleSmallestEigenvalue M hn z := by
  simp only [centralGaussianSampleMinimum,complexNoncentralSampleSmallestEigenvalue,
    complexSampleMatrix_add_mean,zero_add,add_zero]
```

This requires `complexSampleMatrix (z + complexSampleMean M) = complexSampleMatrix z + M` (or similar). The `simp` set must include the lemma that `complexSampleMatrix` distributes over addition in the sample space. If `complexSampleMatrix_add_mean` isn't exactly this statement, the simp will silently fail to close the goal. Verify the lemma exists and has the right shape.

## 4. Fixed mean, no uniformity claim

The docstring correctly states constants depend on the FIXED mean. The definitions `noncentralMinimumPowerLower/Upper` multiply `gaussianShiftLowerConstant (complexSampleMean M)` which contains `exp(-‖complexSampleMean M‖²)`. For any fixed M, this is a positive constant. No issue here. ✓

## 5. Log ratio diversity proof structure

```lean
theorem actualNoncentralMinimumCDF_diversity ...
  apply tendsto_log_ratio_of_power_bounds _ (d+1) ...
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0 : ℝ)<1/4)).filter_mono nhdsWithin_le_nhds]
```

The `filter_upwards` combines:
- `self_mem_nhdsWithin`: x > 0 eventually in 𝓝[>] 0
- The second filter ensures x ≤ 1/4 eventually

Since 𝓝[>] 0 concentrates near 0, eventually x < 1/4 holds. The `nhdsWithin_le_nhds` monotonicity converts the plain nhds eventuality to nhdsWithin. This is correct. ✓

## 6. Rectangular reindexing

```lean
obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
have hm : m-(k+1)+(k+1)=m := Nat.sub_add_cancel hnm
generalize hd : m-(k+1)=d at *
subst m
```

With `n = k+1` and `d = m - n`, we get `m = d + n = d + (k+1)`. The diversity exponent becomes `d+1 = m-n+1`. This matches the stated result `(m-n+1 : ℕ)`. ✓

## 7. High-SNR negative exponent

```lean
tendsto_log_ratio_inverse_threshold _ _ (actualNoncentralMinimumCDF_diversity d n M) b hb
```

If F(x) ~ x^(d+1) as x→0⁺, then F(b/r) ~ (b/r)^(d+1) as r→∞. So log F(b/r) / log r → -(d+1). The sign flip comes from log(1/r) = -log r. Assuming `tendsto_log_ratio_inverse_threshold` is proven generically for any positive exponent, this application is valid. ✓

## Summary of P4 concerns

| # | Issue | Severity |
|---|-------|----------|
| 1 | `by finiteness` in `hlR` — verify it actually discharges the goal | Medium |
| 2 | Ensure `gaussianShiftUpperConstant y ≠ 0` is visible to `ofReal_ne_top` | Low |
| 3 | Confirm `complexSampleMatrix_add_mean` lemma shape matches simp expectation | Medium |
| 4–7 | Logic verified correct | None |

No axioms are introduced beyond the imported comparison theorem. The structure is sound given the premises hold.
