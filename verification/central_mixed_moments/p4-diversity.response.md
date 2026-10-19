# P4 Review: `CentralMinimumDiversity.lean`

## 1. Critical Math Bug: Inverted Squeeze Bounds

In `tendsto_log_ratio_of_power_bounds`, the roles of `c` and `C` are **swapped** in the squeeze theorem application.

Given `c*x^k ≤ f x ≤ C*x^k` and `log x < 0` near 0⁺:
- Dividing by `log x` **flips** inequalities:
  - `(log c + k*log x)/log x ≥ log(f x)/log x ≥ (log C + k*log x)/log x`
  - Simplifying: `k + log c/log x ≥ log(f x)/log x ≥ k + log C/log x`

So `k + log C/log x` is the **lower** bound and `k + log c/log x` is the **upper** bound.

**The code has them backwards:**
```lean
have hl : Tendsto (fun x => (k : ℝ)+Real.log C / Real.log x) ... -- labeled "l" (lower?) but used as upper
have hu : Tendsto (fun x => (k : ℝ)+Real.log c / Real.log x) ... -- labeled "u" (upper?) but used as lower
apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
-- hl passed first = claimed lower bound, but contains C = actual upper bound
```

**Fix:** Swap `hl`/`hu` or swap `c`/`C` in their definitions.

---

## 2. Missing Hypothesis: `k > 0` or Explicit `f > 0` Handling for `k = 0`

The P4 notes state *"Generic log lemma allows k=0 too."* However, when `k = 0`:
- `x^k = 1`, so bounds become `c ≤ f x ≤ C`
- `f x` need not tend to 0, so `log(f x)` doesn't diverge
- The ratio `log(f x)/log x → 0/(-∞) = 0` ✓

This actually works mathematically, but the proof uses `pow_pos hx.1 _` which requires `k ≠ 0` or special handling. For `k = 0`, `x^0 = 1 > 0` still holds, so `pow_pos` is fine. **No issue here**, but worth documenting that `k = 0` is intentionally supported.

---

## 3. Redundant Positivity Proof Obligations

```lean
· positivity  -- proves 0 < Real.exp (-1)/(Nat.factorial (d+1) : ℝ)
· positivity  -- proves 0 < ((n+1 : ℕ) : ℝ)^(d+2)/(Nat.factorial (d+1) : ℝ)
```

These work but are fragile—`positivity` may fail if factorial casting or division lemmas aren't in scope. More robust:
```lean
· exact div_pos (Real.exp_pos _) (Nat.cast_pos.mpr (Nat.factorial_pos _))
· exact div_pos (pow_pos (Nat.cast_add_one_pos n) _) (Nat.cast_pos.mpr (Nat.factorial_pos _))
```

---

## 4. Filter Construction: Unnecessary Complexity

```lean
filter_upwards [hb,(eventually_lt_nhds (by norm_num : (0 : ℝ)<1)).filter_mono nhdsWithin_le_nhds]
  with x hx hx1
```

The second filter just establishes `x < 1` eventually. This could be extracted once from `hb` (which already contains `0 < x ∧ ... ∧ x ≤ 1` information via `actualCentralMinimumCDF_local_power_bounds`). Currently `hx1` duplicates what's implicit in the local bounds hypothesis.

**Not a bug**, but adds noise. Consider whether `hb` alone suffices if you strengthen it to include `x < 1`.

---

## 5. Logarithm Sign Reasoning: Fragile Chain

```lean
have hd : Real.log x < 0 := Real.log_neg hx.1 hx1
...
have h := (div_le_div_of_nonpos_of_le hd.le hlog)
```

`div_le_div_of_nonpos_of_le` requires the denominator to be **nonpositive**. Here `hd.le : log x ≤ 0` (from strict `< 0`). This is correct but:
- If `x = 1` ever entered the filter (it doesn't, due to `nhdsWithin_le_nhds`), `log 1 = 0` would cause division by zero.
- The `hx0 : Real.log x ≠ 0` guard comes **after** its use in `field_simp`.

**Safe in practice** because `𝓝[>] 0` restricted to `x < 1` excludes `x = 1`. But the ordering is confusing—consider moving `hx0` earlier for clarity.

---

## 6. CDF Definition: Correct per P4 Notes

```lean
def actualCentralMinimumCDF (d n : ℕ) (x : ℝ) : ℝ :=
  (stdGaussian (...)).real {z | ... z ≤ x}
```

Confirmed: `.real` extracts `ENNReal.toReal` of the measure applied to the event set. This is a real number, not a measure on ℝ. Matches P4 specification. ✓

---

## 7. No Independence Assumption Used ✓

The `(n+1)^(d+2)` prefactor in the upper bound arises from the deterministic residual inclusion + finite union bound (per P4 notes). The proof correctly never invokes independence of residuals. The `CentralMinimumGammaSandwich` import presumably handles this. **No issue.**

---

## Summary

| # | Severity | Issue |
|---|----------|-------|
| 1 | **Bug** | `hl`/`hu` swapped in squeeze application—proof is incorrect as stated |
| 2 | OK | `k = 0` support works; no change needed |
| 3 | Minor | `positivity` fragility for explicit constants |
| 4 | Style | Redundant filter intersection |
| 5 | Minor | Sign reasoning order could be clearer |
| 6 | OK | CDF definition matches spec |
| 7 | OK | No independence assumption |

**Blocker:** Issue #1 must be fixed before the proof is valid.
