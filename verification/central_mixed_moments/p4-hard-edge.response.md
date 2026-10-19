# P4 Adversarial Review: Gamma Hard-Edge Bounds & Central Minimum Θ(x^(d+1))

## 1. Critical Measure-Theoretic Mismatch in `actualCentralMinimumCDF`

**The definition is ill-typed or hides a coercion.**

```lean
def actualCentralMinimumCDF (d n : ℕ) (x : ℝ) : ℝ :=
  (stdGaussian (ComplexSample (m := d+(n+1)) (n := n+1))).real
    {z | centralGaussianSampleMinimum ... z ≤ x}
```

- `(stdGaussian ...).real` is a `Measure ℝ`, not a function you can apply to a set of `z`. If this intends the measure of the event, it should be `(stdGaussian ...).real {w | ...}` where `w` lives in the correct sample space.
- The set `{z | centralGaussianSampleMinimum ... z ≤ x}` — what is the type of `z`? If `z : ComplexSample`, then `centralGaussianSampleMinimum` returns an `ℝ`, but the predicate mixes the sample `z` with the real threshold `x` in a way that suggests `z` is being treated as both the random outcome and the argument to the minimum function.
- **Hidden assumption**: This silently assumes the event is measurable. No `MeasurableSet` proof is provided. The CDF is only well-defined if `{z | ... ≤ x}` is measurable w.r.t. the Gaussian measure. This is likely true (minimum of continuous functions is measurable), but it's unproven here.

## 2. Variance/Scaling Mismatch in the Upper Bound

**The factor `(n+1)^(d+2)` appears without probabilistic justification.**

In `actualCentralMinimumCDF_power_bounds`, the upper bound:
```lean
actualCentralMinimumCDF d n x ≤ ((n+1 : ℕ) : ℝ)^(d+2)*x^(d+1)/(Nat.factorial (d+1) : ℝ)
```

comes from evaluating `cdf_gammaMeasure_nat_power_upper d (((n+1):ℝ)*x)` and using the sandwich `hs.2`. But:

- The imported sandwich `actualCentral_minimum_gamma_sandwich` relates the minimum CDF to a **single** Gamma CDF at scale `(n+1)*x`. This implicitly encodes a union bound over `N = n+1` columns, each contributing a factor.
- **The exponent `d+2` is suspicious**: `mul_pow` gives `((n+1)*x)^(d+1) = (n+1)^(d+1) * x^(d+1)`, then multiplied by another `(n+1)` from the sandwich yields `(n+1)^(d+2)`. But where does the extra `(n+1)^1` come from in the sandwich itself? If the sandwich states `P(min ≤ x) ≤ (n+1) * P(Gamma ≤ (n+1)*x)`, that's a union bound times a scaling — but the scaling of the Gamma argument by `(n+1)` **inside the CDF** already accounts for the eigenvalue scaling. Having both a prefactor `(n+1)` and an argument scaling `(n+1)*x` double-counts unless the sandwich theorem explicitly justifies this form.
- **Concrete issue**: Verify that `actualCentral_minimum_gamma_sandwich` actually states:
  ```
  cdf gamma x ≤ actualCDF x ≤ (n+1) * cdf gamma ((n+1)*x)
  ```
  and not `... ≤ cdf gamma ((n+1)*x)` (without the prefactor). If there's no prefactor, the `(n+1)^(d+2)` should be `(n+1)^(d+1)`.

## 3. Filter Mismatch: `nhdsGT 0` vs. Global `x ≥ 0` Bounds

**The local bounds require `x ≤ 1` but the Θ statement doesn't reflect this restriction clearly enough.**

- `actualCentralMinimumCDF_local_power_bounds` requires `hx1 : x ≤ 1` to get `exp(-x) ≥ exp(-1)`.
- The `eventually` filter in the Θ proof correctly restricts to `x < 1` via `eventually_lt_nhds (0 < 1)`. This is fine.
- **But**: the lower constant `c = exp(-1)/(d+1)!` is only valid on `(0,1]`. The Θ result is stated for `𝓝[>] 0`, which is correct — but if anyone uses this theorem expecting the constants `c, C` to work globally for all `x > 0`, they'll be wrong. The theorem statement is fine; the **documentation** is misleading when it says "explicit hard-edge power bounds" without emphasizing the local nature.

## 4. Hidden Assumption: `n > 0` Means `N ≥ 2`, Not `N ≥ 1`

The spec says "n>0 here means N≥2" where `N = n+1`. So `hn : 0 < n` gives `n ≥ 1`, hence `N = n+1 ≥ 2`. This is consistent. But:

- **What about `d = 0`?** All theorems quantify over `d : ℕ` with no positivity constraint. When `d = 0`, `gammaMeasure 1 1` is `Exp(1)`, and the bounds become `exp(-x)*x ≤ CDF ≤ (n+1)^2 * x`. This is mathematically correct but verify that `Nat.succ_pos d` (used in `cdf_gammaMeasure_nat_eq_lowerGamma`) handles `d=0`: it gives `0 < 1`, which is fine.
- **No hidden issue here**, but worth noting `d=0` is included.

## 5. Measurability / ENNReal.toReal_nonneg Abuse

In the Θ proof:
```lean
have hF : 0 ≤ actualCentralMinimumCDF d n x := ENNReal.toReal_nonneg
```

- `ENNReal.toReal_nonneg` proves `0 ≤ μ.toReal` for any `ENNReal` measure `μ`. But `actualCentralMinimumCDF` is defined as a direct `ℝ`-valued function (the `.real` projection of a measure applied to a set). If the measure application returns `⊤` (infinite measure, impossible for a probability measure but Lean doesn't know that automatically), `.toReal` would give `0`, and the nonnegativity still holds.
- **Concrete issue**: This relies on `stdGaussian` being a finite (probability) measure so that `.real {set}` is actually the probability in `[0,1]`. If the formalization hasn't proven `IsProbabilityMeasure (stdGaussian ...)`, then `ENNReal.toReal_nonneg` is technically correct (it's always `≥ 0`) but semantically vacuous — the "CDF" might not be a CDF.

## 6. Integral Comparison Logic in `cdf_gammaMeasure_nat_power_upper`

```lean
exact mul_le_of_le_one_right (pow_nonneg hu.1 d) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu.1))
```

- `hu : u ∈ Set.Icc 0 x`, so `hu.1 : 0 ≤ u`. Then `exp(-u) ≤ 1` because `-u ≤ 0`. Correct.
- `u^d * exp(-u) ≤ u^d * 1 = u^d`. Correct.
- **No issue** in the Gamma bounds themselves. These are clean analytic inequalities.

## 7. Missing Event Equivalence Proof

The entire development rests on `actualCentral_minimum_gamma_sandwich` connecting:
- **Event A**: `{z | centralGaussianSampleMinimum ... z ≤ x}` (minimum of `N` dependent quadratic forms)
- **Event B**: Gamma CDF evaluation (sum of `d+1` independent `Exp(1)` variables)

The review prompt states: "Imported checked Gamma sandwich comes from actual independent CN(0,1) source and AE fullrank, **no residual independence**."

- **This is the key hidden assumption**: The sandwich theorem must handle the fact that after projecting onto the orthogonal complement (residual), the resulting quadratic forms are **not independent** of each other or of the original columns. If the sandwich proof assumed independence at the residual step, it's unsound.
- Since we're told it's "checked" and uses "AE fullrank", assume this is handled — but verify that the sandwich constants don't silently assume `N` independent copies rather than `N` correlated copies with a rank correction.

## Summary of Concrete Issues

| # | Severity | Issue |
|---|----------|-------|
| 1 | **High** | `actualCentralMinimumCDF` definition is syntactically/semantically unclear — mixing measure application with set comprehension without explicit measurability |
| 2 | **High** | Upper bound exponent `(n+1)^(d+2)` may double-count union bound + scaling; verify against exact statement of `actualCentral_minimum_gamma_sandwich` |
| 3 | **Medium** | Θ constants only valid locally on `(0,1]`; documentation doesn't flag this |
| 4 | **Low** | `d=0` case works but is undocumented |
| 5 | **Medium** | `ENNReal.toReal_nonneg` used without establishing `stdGaussian` is a probability measure |
| 6 | **None** | Gamma integral bounds are correct |
| 7 | **Critical** | Sandwich theorem soundness depends on handling residual dependence — cannot be verified from these files alone |

**Bottom line**: The Gamma CDF bounds (file 1) are analytically sound. The central minimum Θ result (file 2) has a well-defined filter structure but rests on two unverified pillars: the precise statement of the imported sandwich theorem (especially the `(n+1)` prefactor vs. argument scaling), and the measurability/probability-measure status of the CDF definition. No sharp prefactor or noncentral claim is made, which is appropriate.
