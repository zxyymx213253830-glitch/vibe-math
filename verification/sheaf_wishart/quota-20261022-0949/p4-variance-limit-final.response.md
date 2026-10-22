# P4 Adversarial Review

## SOURCE 1: MeanSquareSecondMomentContinuity.lean

**Mathematical gap (minor): `hu.integrable_sq` / `hv.integrable_sq` API availability.**
The proof uses `hu.integrable_sq` to derive `Integrable (fun a => (u a)^2) μ` from `MemLp u 2 μ`. This is mathematically correct (L² membership means the square is integrable), but the exact dot-notation field may not exist as written depending on the Mathlib version. This is an API-level concern, not a logical gap—the underlying mathematical step is sound.

**Condition `1 ≤ r` in `hu`: unnecessary restriction or intentional?**
The hypothesis `hu : ∀ r : ℝ, 1 ≤ r → MemLp (u r) 2 μ` restricts L² membership to `r ≥ 1`, yet the limit `Tendsto ... atTop` only needs eventual behavior. This is mathematically fine since `atTop` eventually satisfies `r ≥ 1`. No gap—just noting the condition is tighter than needed but harmless.

**No other mathematical issues.** The algebraic identity `(u)² - (v)² = (u-v)² + 2(u-v)v` is correctly applied, Cauchy-Schwarz/Hölder usage is valid, and the squeeze theorem application is sound.

---

## SOURCE 2: ActualSingularLogDetVarianceLimit.lean

**Mathematical gap: `R` definition mixes `ℕ` and `ℝ` without explicit coercion clarity.**
```lean
let R : ℝ := (min m (Matrix.fromRows B M).rank : ℕ)
```
This casts a `ℕ` to `ℝ`, which is fine, but then `R * Real.log r` treats `R` as real. No actual gap—Lean coerces `ℕ → ℝ` automatically. However, if `m = 0` or `rank = 0`, then `R = 0` and the offset vanishes. The theorems still hold trivially, but this edge case should be noted.

**Potential gap: `hC.sub hS` strong measurability.**
In `hE`, the proof writes `(memLp_two_iff_integrable_sq (hC.sub hS).aestronglyMeasurable)`. The subtraction of two integrable functions yields an integrable function, and `.aestronglyMeasurable` extracts measurability. This is correct provided `hC.sub hS` produces an `Integrable` object with that field. Mathematically sound; API-dependent but not logically broken.

**Actual concern: `convert hE.add hSM using 1` followed by pointwise ring.**
The proof converts `MemLp (U r - S) 2` plus `MemLp S 2` into `MemLp (U r) 2` via `add`, then uses `funext z; dsimp; ring` to show `(U r z - S z) + S z = U r z`. This is **mathematically correct**—no gap.

**Variance theorem (`variance_tendsto`): `hmean.pow 2` limit arithmetic.**
The step `have ht := hU.2.sub (hmean.pow 2)` subtracts limits: if `∫(U r)² → ∫S²` and `∫U r → ∫S`, then `Var(U r) = ∫(U r)² - (∫U r)² → ∫S² - (∫S)² = Var(S)`. This is **correct** by continuity of subtraction and squaring. No gap.

**`ProbabilityTheory.variance_sub_const` applicability.**
Used to show `Var(U r) = Var(actualCorrelatedMatrixLogDet B M r)` since they differ by constant `R * log r`. Correct—variance is translation-invariant. Requires the function to have finite variance, which is guaranteed by `MemLp ... 2`. Sound.

---

## Summary

| Source | Issue Type | Description |
|--------|-----------|-------------|
| S1 | API question | `hu.integrable_sq` dot notation availability |
| S2 | Edge case | `R = 0` when `m = 0` or rank is zero (trivially handled) |
| S2 | API question | `.aestronglyMeasurable` field access on `Integrable` |

**Verdict:** No actual mathematical gaps. Both proofs are logically sound given their stated assumptions. All concerns are API/surface-level, not semantic.
