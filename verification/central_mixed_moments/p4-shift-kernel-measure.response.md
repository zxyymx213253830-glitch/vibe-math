I'll review these two files for P4 issues (correctness bugs) only, without using tools or rewriting.

## Review of `GaussianShiftKernelBounds.lean`

**1. Exponent bounds are incorrect (P4)**

In `gaussian_shift_exponent_bounds`, the claimed inequality:
```
-‖y‖^2 - 2*‖x‖^2 ≤ -‖x-y‖^2/2 ∧ -‖x-y‖^2/2 ≤ ‖y‖^2 - ‖x‖^2/8
```

The second conjunct is wrong. From `h2` you get `‖x-y‖^2 ≤ 2*‖x‖^2 + 2*‖y‖^2` (after simplification), which gives `-‖x-y‖^2/2 ≥ -‖x‖^2 - ‖y‖^2`. But the upper bound claimed is `-‖x-y‖^2/2 ≤ ‖y‖^2 - ‖x‖^2/8`. The coefficient `-1/8` on `‖x‖^2` cannot come from `nlinarith [sq_nonneg ‖x‖, sq_nonneg ‖y‖]` applied to `h1` and `h2`. This looks like it was tuned to match a desired kernel form rather than derived.

However — checking the downstream use in `euclideanStdGaussianDensity_shift_bounds`: the right-hand side uses `exp(‖y‖^2) * phi(x/2)`, meaning exponent `‖y‖^2 - ‖x/2‖^2/2 = ‖y‖^2 - ‖x‖^2/8`. So the arithmetic is actually **consistent with the stated density bound**, but the lemma `gaussian_shift_exponent_bounds` itself is not provable from the given `nlinarith` call as written. The `nlinarith` will fail because `-1/8` doesn't follow from the inputs. **This is a P4 bug: the proof does not establish the claim.**

**2. Density bound signs are correct**

Given the exponent bound (if it held), the density comparison logic is fine:
- Left: `exp(-‖y‖^2) * exp(-4‖x‖^2/2) = exp(-‖y‖^2 - 2‖x‖^2)` vs `exp(-‖x-y‖^2/2)` ✓
- Right: `exp(-‖x-y‖^2/2)` vs `exp(‖y‖^2) * exp(-‖x‖^2/8)` ✓

The constant factor handling with `hc` is correct.

**3. No issue with dimension-0 case**

`Fintype.card ι = 0` gives `(sqrt(2π))⁻¹ ^ 0 = 1`, which is fine.

---

## Review of `GaussianShiftMeasureComparison.lean`

**4. Jacobian inversion is backwards (P4)**

In `stdGaussian_smul_eq_density`, the map is `z ↦ r • z`. The pushforward density should involve `|r|^{-D}` times the original density evaluated at `r⁻¹ • z`. The code writes:
```
abs (r^Fintype.card ι)⁻¹ * euclideanStdGaussianDensity (r⁻¹ • z)
```
This is `|r^D|⁻¹ = |r|^{-D}`, which is **correct** for the Jacobian determinant of the inverse map.

**5. Lower bound: `ofReal` order and smul direction (P4)**

In `stdGaussian_shift_measure_lower`:
```
ENNReal.ofReal (((2 : ℝ)^Fintype.card ι)⁻¹ * Real.exp (-‖y‖^2)) • ...map (fun z => (1/2 : ℝ) • z) ≤ ...map (fun z => z+y)
```

The scalar `(2^D)⁻¹ * exp(-‖y‖^2)` is positive, so `ofReal` is fine. But check the math: from the pointwise bound `exp(-‖y‖^2) * phi(2x) ≤ phi(x-y)`, integrating against the half-scaled measure means we need the density of `map(z ↦ z/2)` which is `2^D * phi(2x)`. So the lower bound on `Law(Z+y)` relative to `Law(Z/2)` should be `exp(-‖y‖^2) / 2^D`, i.e., `(2^D)⁻¹ * exp(-‖y‖^2)`. **This matches.** ✓

**6. Upper bound: exponent sign error (P4)**

In `stdGaussian_shift_measure_upper`:
```
ENNReal.ofReal ((2 : ℝ)^Fintype.card ι * Real.exp (‖y‖^2)) • ...map (fun z => (2 : ℝ) • z)
```

From the pointwise bound `phi(x-y) ≤ exp(‖y‖^2) * phi(x/2)`, the density of `map(z ↦ 2z)` is `2^{-D} * phi(x/2)`. So `Law(Z+y) ≤ exp(‖y‖^2) * 2^D * Law(2Z)`. The code has `2^D * exp(‖y‖^2)`. **This matches.** ✓

**7. `withDensity_smul` argument order (potential P4)**

The line `rw [← withDensity_smul _ (by unfold euclideanStdGaussianDensity; fun_prop)]` — the `_` placeholder needs to resolve to the correct function. If `withDensity_smul` expects the scalar first and the function second (or vice versa), this could silently swap arguments. Without seeing the exact signature of `withDensity_smul` from your library, I flag this as a **potential P4** if the elaborator picks up a wrong unification.

**8. `convert ... using 1` fragility (P4 risk)**

The `convert (euclideanStdGaussianDensity_shift_bounds z y).1 using 1` relies on `field_simp` closing the remaining goal. If there's any mismatch in how `abs`, `inv`, or power associativity normalizes between LHS and RHS, `field_simp` may leave a non-trivial residue. Given the explicit `hj` rewrite and `norm_num only [one_div, inv_inv]`, this should work, but the `using 1` depth limit means it won't look deeper than one layer. **Low risk but worth noting.**

**9. Missing nonnegativity side-condition on `ofReal_mul` (P4)**

`ENNReal.ofReal_mul (by positivity)` — the `positivity` tactic must confirm the first argument to `ofReal_mul` is non-negative. In the lower bound, `((1/2)^D)⁻¹ = 2^D > 0` and `exp(...) > 0`, so this is fine. In the upper bound, same reasoning. **No bug here.** ✓

---

## Summary of P4 Issues

| # | File | Issue | Severity |
|---|------|-------|----------|
| 1 | KernelBounds | `gaussian_shift_exponent_bounds` second conjunct (`-‖x‖^2/8`) is not derivable from the stated `nlinarith` premises; proof will fail | **Critical** |
| 7 | MeasureComparison | `withDensity_smul _` placeholder may unify incorrectly depending on library signature | **Medium** |
| 8 | MeasureComparison | `convert ... using 1` + `field_simp` is fragile if normalization doesn't align exactly | **Low** |

Issue #1 is the only definite correctness bug: the exponent `-1/8` coefficient on `‖x‖^2` in the upper bound doesn't follow from `norm_sub_square_le_twice` alone. You'd need an additional inequality or a different decomposition to justify that specific constant.
