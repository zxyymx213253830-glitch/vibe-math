# P4 Concrete Issues: CentralMinimumAllShapesDiversity & CentralMinimumScaledDiversity

## 1. Dimensional Transport: `m` vs `d+(n+1)` Mismatch (Scaled File)

**File:** `CentralMinimumScaledDiversity.lean`, definition + all theorems
**Issue:** The sample space is `ComplexSample (m := d+(n+1)) (n := n+1)`, but the diversity exponent throughout is `d+1`. This means total columns `N = n+1`, previous columns `n`, and the minimum eigenvalue dimension gap is `m - N + 1 = (d+n+1) - (n+1) + 1 = d+1`. **This is correct**, but the definition hardcodes `n+1` as the second parameter while using `n` as the free variable in theorems. The transport from `actualCentralMinimumCDF d n` (which uses `m=d+1, n=1` when `n=0`, or general `m=d+n+1, n=n+1`) to the scaled version conflates the **shape parameter** `n` (previous columns) with the **Lean function argument** `n`.

**Concrete symptom:** `actualCentralCovarianceMinimumCDF d n v x` calls `centralGaussianSampleMinimum (d+(n+1)) (n+1) (Nat.succ_pos n)`. The proof `Nat.succ_pos n` is always true, but when the caller intends `n=0` (scalar/one-column case), this becomes `centralGaussianSampleMinimum (d+1) 1 (by decide)`, which is fine. However, the **unscaled** `actualCentralMinimumCDF d n` uses `m := d+n+1, n := n+1` internally only after the `cases n` split in `_all_local_power_bounds`. The definition itself doesn't enforce this coupling.

**Fix required:** Either:
- Make the dimensional relationship explicit: add a hypothesis `hmn : m = d + n + 1` or
- Rename the function parameter from `n` to `k` where `N = k + 1` total columns, preventing confusion with the `n` in `actualCentralMinimumCDF d n`.

---

## 2. Scalar Branch: `.real` vs `.toReal` Inconsistency

**File:** `CentralMinimumAllShapesDiversity.lean`, `actualCentralMinimumCDF_oneColumn`
**Issue:** The proof uses `.toReal` in the `change` statement:
```lean
change ((stdGaussian ...).{z | ... ≤ x}).toReal = (((stdGaussian ...).map ...).Iic x).toReal
```
But `actualCentralMinimumCDF` is defined via `.real` (from `CentralMinimumDiversity` import, presumably `μ.real s = μ.toReal s` for probability measures). The `rw [cdf_eq_real]` suggests `cdf` outputs `.real`, yet the `change` targets `.toReal`.

**Concrete problem:** If `Measure.real` is notation for `.toReal` (as stated in your instructions: "Measure.real is mu(event).toReal, NOT measure on R"), then `cdf_eq_real` should produce `.toReal`. But `Measure.map_apply` produces an equality of **measures applied to sets**, returning `ENNReal`. The `.toReal` coercion happens **after** the map. The `rfl` at the end only closes if both sides are definitionally equal post-coercion, which requires that `cdf` already unfolded to `.toReal` of the same preimage.

**Risk:** If `cdf` is defined as `fun x => (μ (Iic x)).toReal` but the map_apply gives `(μ.map f) (Iic x) = μ (f ⁻¹' Iic x)`, then `rfl` works. But if there's any `ENNReal.ofReal` / `.toReal` round-trip, `rfl` may mask a side condition about finiteness.

**Fix required:** Replace `rfl` with an explicit `congr_arg ENNReal.toReal` after `rw [Measure.map_apply ...]`, or add a comment justifying why the ENNReal values are finite (they're probabilities ≤ 1).

---

## 3. `v` vs `sqrt(v)` Scaling: Missing Positivity Filter in Scaled CDF Definition

**File:** `CentralMinimumScaledDiversity.lean`, `actualCentralCovarianceMinimumCDF`
**Issue:** The definition applies `Real.sqrt v • z` without requiring `0 < v` in the signature. When `v ≤ 0`, `Real.sqrt v = 0`, so the scaling collapses all samples to zero, and the event `{z | centralGaussianSampleMinimum ... (0 • z) ≤ x}` becomes either everything or nothing depending on `x ≥ 0`. The theorems correctly add `hv : 0 < v`, but the **definition itself is silent**.

**Concrete transport error:** In `actualCentralCovarianceMinimumCDF_eq`, the rewrite uses `centralGaussianSampleMinimum_scale _ _ _ (Real.sqrt v) (Real.sqrt_pos.mpr hv)`. This lemma requires the scalar to be positive. If someone unfolds the definition without `hv`, they get stuck.

**Fix required:** Either:
- Add `(hv : 0 < v)` to the def signature (making it a dependent definition), or
- Use `√(max v 0)` with a documented convention that `v > 0` is the physical regime.

---

## 4. Outage Threshold `b/r`: Hidden Assumption `r > b` for `log(b/r) < 0`

**File:** `CentralMinimumScaledDiversity.lean`, `tendsto_log_ratio_inverse_threshold`
**Issue:** The proof uses:
```lean
have hlt : b/r < 1 := (div_lt_one (hb.trans hr)).mpr hr
have hlog : Real.log (b/r) ≠ 0 := (Real.log_neg hp hlt).ne
```
This requires `r > b` (ensured by `eventually_gt_atTop b`). **Correct.** But the `field_simp` step after uses `Real.log_div hb.ne' (by linarith : r ≠ 0)`, which expands `log(b/r) = log b - log r`. The subsequent division by `Real.log r` (implicit in the ratio) requires `log r ≠ 0`, i.e., `r ≠ 1`. The filter `eventually_gt_atTop b` only ensures `r > b > 0`, not `r > 1`.

**Concrete gap:** If `0 < b < 1`, then `eventually_gt_atTop b` includes the interval `(b, 1)` where `log r < 0`. The `field_simp` is still valid (since `r > 0`), but the **sign** of `log r` matters for interpreting the ratio `log(f(b/r))/log r` as an outage exponent. The limit `atTop` avoids this, but intermediate rewrites don't filter `r > 1`.

**Fix required:** Strengthen the filter to `eventually_gt_atTop (max b 1)` or add a line:
```lean
filter_upwards [eventually_gt_atTop (max b 1)] with r hr
```
before the `field_simp` to ensure `log r > 0`.

---

## 5. Log-Bound Direction: Constants `C` and `c` Are Shape-Dependent, Not Universal

**File:** `CentralMinimumAllShapesDiversity.lean`, `actualCentralMinimumCDF_all_local_power_bounds`
**Issue:** The lower bound constant `Real.exp (-1)/(Nat.factorial (d+1))` and upper bound `((n+1)^(d+2))/(Nat.factorial (d+1))` both depend on `n`. The generic log-bound lemma (`tendsto_log_ratio_of_power_bounds`) requires **fixed** positive constants `c, C` independent of `x` but possibly dependent on parameters. Here, for each fixed `d, n`, they're constants—**correct**. But the `cases n` split in the proof reveals that the `n=0` branch derives different constants than the `n=succ` branch (using Gamma CDF bounds vs. the general power bounds).

**Concrete issue:** The `n=0` upper bound simplifies to `1/(Nat.factorial (d+1)) * x^(d+1)` (since `((0+1)^(d+2)) = 1`), but the proof obtains it via `cdf_gammaMeasure_nat_power_upper` which may have a **different** constant. The `simpa only [zero_add, Nat.cast_one, one_pow, one_div, inv_mul_eq_div]` forces agreement, but if `cdf_gammaMeasure_nat_power_upper` actually returns `1/((d+1)!)*x^(d+1)` without the `1^...` factor, the rewrite is fragile.

**Fix required:** Verify that `cdf_gammaMeasure_nat_power_upper d x hx.le` literally equals `x^(d+1)/(Nat.factorial (d+1))` (no extra factors). If it has `Real.exp(-x)` residuals, the `simpa` won't close.

---

## 6. Probability Measure Instance: Scalar Branch Uses Global `gammaMeasure` Instance

**File:** `CentralMinimumAllShapesDiversity.lean`, `actualCentralMinimumCDF_oneColumn`
**Issue:** The `letI : IsProbabilityMeasure (gammaMeasure ((d+1 : ℕ) : ℝ) 1)` is constructed inline. The rate parameter is `1`. But `centralColumnSmallestEigenvalue_map_eq_gammaMeasure` likely produces `gammaMeasure (d+1) 1` only for **standard** complex Gaussian (variance 1 per real dimension). If the imported `WishartGamma` defines `gammaMeasure shape rate` with rate ≠ scale convention, this is fine. But if there's a `2` or `1/2` factor (common in complex Wishart literature where eigenvalues of `Z*Z` for `Z ~ CN(0,I)` give `Gamma(m, 1)` vs `Gamma(m, 1/2)` depending on convention), the `1` here may be wrong.

**Concrete check needed:** Confirm that `stdGaussian (ComplexSample ...)` paired with `centralGaussianSampleMinimum` produces minimum eigenvalue whose law is `gammaMeasure (d+1) 1` **with rate = 1**, not rate = 1/2 or 2. The `rw [cdf_eq_real, ← centralColumnSmallestEigenvalue_map_eq_gammaMeasure (Nat.succ_pos d)]` will typecheck regardless, but the numerical value of the CDF changes.

---

## Summary Table

| # | File | Location | Issue | Severity |
|---|------|----------|-------|----------|
| 1 | Scaled | Def + all | `n` parameter conflation with total columns | Medium |
| 2 | AllShapes | `_oneColumn` | `.real` vs `.toReal` + `rfl` fragility | Low-Medium |
| 3 | Scaled | Def | `sqrt v` undefined behavior for `v ≤ 0` | Low (theorems guard it) |
| 4 | Scaled | `_inverse_threshold` | `log r` sign unfiltered near `r ∈ (b,1)` | **High** |
| 5 | AllShapes | `_all_local_power_bounds` | Constant matching across `cases n` branches | Medium |
| 6 | AllShapes | `_oneColumn` | Gamma rate convention unverified | Medium |

**Priority:** Issue 4 can cause the high-SNR diversity proof to fail at runtime if Lean's simplifier takes a path through `r ∈ (0,1)`. Fix the filter threshold first.
